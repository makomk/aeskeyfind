// AESKeyFinder 1.0 (2008-07-18)
// By Nadia Heninger and Ariel Feldman
// Hacked 2017-05-11 by Aidan Thornton to know more key schedules
// With code from axTLS by Cameron Rich

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <errno.h>
#include <string.h>

extern char *optarg;
extern int optind, opterr, optopt;
#include <getopt.h>

#ifdef __FreeBSD__
#include <err.h>
#else
#define err(x,y) { perror(y); exit(x); }
#endif

#include "util.h"
#include "aes.h"

#define DEFAULT_THRESHOLD 10
static long int gThreshold = DEFAULT_THRESHOLD;
static int gVerbose = 0;
static int gProgress = 1;

#define TWEAK_INVMIXCOLUMN 0x1
#define TWEAK_REVERSE_ORDER 0x2
#define MAX_TWEAKS 0x4

// Print a key, assuming the key schedule starts at map[0].  
// num_bits should be 128 or 256 
// if gVerbose is on it will print the entire key schedule as well 
// as the constraints--the XOR of words that should XOR to 0
static void print_key(uint32_t* map, int num_bits, size_t address)
{
    if (gVerbose) {
        printf("FOUND POSSIBLE %d-BIT KEY AT BYTE %zx \n\n", num_bits, address);
        printf("KEY: ");
    }

    int num_words = num_bits/32;
    for (int col = 0; col < num_words; col++)
        print_word(map[col]);
    printf("\n");


    if (gVerbose) {
        printf("\n");
        printf("EXTENDED KEY: \n");

        int num_roundkeys = 0;
        if (num_bits == 256) num_roundkeys = 15;
        if (num_bits == 128) num_roundkeys = 11;
        for (int row=0; row<num_roundkeys; row++) {
            for (int column = 0; column<4; column++) {
                print_word(map[(4*row+column)]);
            }
            printf("\n");
        }

        printf("\n");
        printf("CONSTRAINTS ON ROWS:\n");

        for (int row=1; row<num_roundkeys; row++) {
            for (int column = 0; column<num_words; column++) {
                if (num_bits == 256 && row == 7 && column >= 4) break;
                if (column==0)
                    print_word(key_core(map[num_words*row-1],row) ^
                            map[num_words*(row-1)] ^
                            map[num_words*row]);
                else if (column == 4)
                    print_word(sbox_bytes(map[num_words*row+3]) ^
                            map[num_words*(row-1)+4] ^
                            map[num_words*row+4]);
                else
                    print_word(map[num_words*row+column-1] ^
                            map[num_words*(row-1)+column] ^
                            map[num_words*row + column]);
            }
            printf("\n");
        }
        printf("\n");
    }
}

// Simple entropy test
//
// Returns true if the 176 bytes starting at location bmap[i] contain
// more than 8 repeats of any byte.  This is a primitive measure of
// entropy, but it works well enough.  The function keeps track of a
// sliding window of byte counts.
static int entropy(const uint8_t* bmap, size_t i)
{
    static int new_call = 1;
    static int byte_freq[256] = {0};
    if (new_call) {
        for (int i=0; i<176; i++) byte_freq[bmap[i]]++;
        new_call = 0;
    }

    int test = 0;
    for (int b=0; b<=0xFF; b++) {
        if (byte_freq[b] > 8) {
            test = 1;
            break;
        }
    }
    byte_freq[bmap[i]]--;
    byte_freq[bmap[i+176]]++;
    return test;
}

// Prints info about the program's command line options
static void usage()
{
    fprintf(stderr, "Usage: aeskeyfind [OPTION]... MEMORY-IMAGE\n"
			"Locates scheduled 128-bit and 256-bit AES keys in MEMORY-IMAGE.\n"
			"\n"
			"\t-v\t\tverbose output -- prints the extended keys and \n"
            "\t\t\tthe constraints on the rows of the key schedule\n"
			"\t-q\t\tdon't display a progress bar\n"
			"\t-t THRESHOLD\tsets the maximum number of bit errors allowed \n"
            "\t\t\tin a candidate key schedule (default = %d)\n"
			"\t-h\t\tdisplays this help message\n", DEFAULT_THRESHOLD);
}

// Prints the progress to stderr
static void print_progress(size_t percent)
{
    fprintf(stderr, "Keyfind progress: %zu%%\r", percent);
}

static unsigned char AES_xtime(uint32_t x)
{
	return (x&0x80) ? (x<<1)^0x1b : x<<1;
}

// converts a key schedule that's had InvMixColumn pre-applied as
// an optimisation for decryption back to a normal key schedule
static void unconvert_key(uint32_t *k, int rounds)
{
    int i;
    uint32_t w, tmp1, old_a0, a0, a1, a2, a3;

    k += 4;

    for (i= rounds*4; i > 4; i--)
    {
        w= *k;

	// note: a quirk of aeskeyfind is that the bytes are in
	// reverse order within the word compared to normal AES
	a3 = (uint32_t)((w>>24)&0xFF);
	a2 = (uint32_t)((w>>16)&0xFF);
	a1 = (uint32_t)((w>>8)&0xFF);
	a0 = (uint32_t)(w&0xFF);

	tmp1 = a0 ^ a1 ^ a2 ^ a3;
	old_a0 = a0;
	a0 ^= tmp1 ^ AES_xtime(a0 ^ a1);
	a1 ^= tmp1 ^ AES_xtime(a1 ^ a2);
	a2 ^= tmp1 ^ AES_xtime(a2 ^ a3);
	a3 ^= tmp1 ^ AES_xtime(a3 ^ old_a0);

	*k++ =  ((a3 << 24) | (a2 << 16) | (a1 << 8) | a0);
    }
}


// The core key finding loop
//
// Searches for AES keys in memory image bmap with starting offsets up
// to last; prints any keys found
static void find_keys(const uint8_t* bmap, size_t last)
{
    size_t percent = 0;
    const size_t increment = last / 100;

    if (gProgress)
        print_progress(percent);

    for (size_t i = 0; i < last; i++) {
        if (entropy(bmap,i)) continue;

        uint32_t* map = (uint32_t*)&(bmap[i]);

        // Check distance from 256-bit AES key
	// FIXME: implement tweaks here too
        int xor_count_256 = 0;
        for (size_t row = 1; row < 8; row++) {
            for (size_t column = 0; column < 8; column++) {
                if (row == 7 && column == 4) break;
                if (column == 0)
                    xor_count_256 += popcount(key_core(map[8*row-1],row) ^
                            map[8*(row-1)] ^
                            map[8*row]);
                else if (column == 4)
                    xor_count_256 += popcount(sbox_bytes(map[8*row+3])^
                            map[8*(row-1)+4] ^
                            map[8*row+4]);
                else
                    xor_count_256 += popcount(map[8*row+column-1] ^
                            map[8*(row-1)+column] ^
                            map[8*row + column]);
            }
	    if (xor_count_256 > gThreshold)
	      break;
        }
        if (xor_count_256 <= gThreshold)
            print_key(map,256,i);

	for(int tweaks = 0; tweaks < MAX_TWEAKS; tweaks++) {
	    // Try various tweaks to how key schedule is storted
	    uint32_t newmap[4*11];
	    map = (uint32_t*)&(bmap[i]);
	    if(tweaks & TWEAK_REVERSE_ORDER)
		for (size_t row = 0; row < 11; row++)
		    memcpy(newmap+4*row, map+4*(10-row), 4*sizeof(uint32_t));
	    else
		memcpy(newmap, map, 4*11*sizeof(uint32_t));
	    map = newmap;
	    if(tweaks & TWEAK_INVMIXCOLUMN)
		unconvert_key(map, 10);

	    // Check distance from 128-bit AES key
	    int xor_count_128 = 0;
	    for (size_t row = 1; row < 11; row++) {
		for (size_t column = 0; column < 4; column++) {
		    if (column == 0)
			xor_count_128 += popcount(key_core(map[4*row-1],row) ^
						  map[4*(row-1)] ^
						  map[4*row]);
		    else
			xor_count_128 += popcount((map[4*row + column-1] ^
						   map[4*(row-1)+column]) ^
						  map[4*row + column]);
		}
		if (xor_count_128 > gThreshold)
		    break;
	    }
	    if (xor_count_128 < gThreshold)
		print_key(map,128,i);
	}

        if (gProgress) {
            size_t pct = (increment > 0) ? i / increment : i * 100 / last;
            if (pct > percent) {
                percent = pct;
                print_progress(percent);
            }
        }
    }

    if (gProgress) {
        print_progress(100);
        fprintf(stderr, "\n");
    }
}

// Memory maps filename and return a pointer on success, setting len
// to the length of the file (does not return on error)
unsigned char *map_file(char *filename, size_t *len) {
  int fd = open(filename, O_RDONLY);
  if (fd < 0)
    err(1, "image open failed");

  struct stat st;
  if (fstat(fd, &st) != 0)
    err(1, "image fstat failed");

  unsigned char *map;
  map = (unsigned char*)mmap(0, st.st_size, PROT_READ, MAP_SHARED, fd, 0);
  if (map == MAP_FAILED)
    err(1, "image mmap failed");

  *len = st.st_size;
  return map;
}

int main(int argc, char * argv[])
{
    int ch = -1;
    while ((ch = getopt(argc, argv, "hvqt:")) != -1) {
        switch(ch) {
            case 'v':
                gVerbose = 1;
                break;
            case 'q':
                gProgress = 0;
                break;
            case 't':
                {
                    errno = 0;
                    char* endptr = NULL;
                    gThreshold = strtol(optarg, &endptr, 10);
                    if (gThreshold < 0 || errno != 0 || endptr == optarg) {
                        fprintf(stderr, "invalid threshold\n");
                        usage();
                        exit(1);
                    }
                }
                break;
            case '?':
            case 'h':
            default:
                usage();
                exit(1);
        }
    }

    argc -= optind;
    argv += optind;

    if (argc != 1) {
        usage();
        exit(1);
    }

    size_t len;
    unsigned char *image = map_file(argv[0], &len);
    if (len < 240) {
        fprintf(stderr, "memory image too small\n");
        exit(1);
    }

    find_keys(image, len - 240);

    return 0;
}
