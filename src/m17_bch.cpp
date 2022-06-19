/*
 * This is a simple BCH encoder and decoder for the BCH primitive (511,385,14) code
 *
 * written by C.H Brain G4GUO 12th June 2022
 *
 * You may use this program or it's derivatives without credit.
 * There is no restriction on what applications this code can be used for.
 *
 * The program bears no copyright
 *
 * The author bears no responsibility for its correctness or it's functioning
 *
 */
#include <memory.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <sys/time.h>

#define BCH_N  511
#define BCH_K  385
#define BCH_NK 126
#define BCH_M  9
#define BCH_T  14
#define BCH_2T (2*BCH_T)
#define SM     (BCH_2T+1)
#define GP_SIZE 0x200
#define GT_SIZE 0x220
#define GP_MASK 0x1FF

#define ginv(a)    m_pinv[a]
#define gpwrn(a,b) (cgmpwr(a,b))
#define gadd(a,b)  (a^b)

static uint64_t m_64_poly[2];
static uint16_t m_pinv[GP_SIZE];
static uint16_t m_gmod;

static uint16_t cmult(uint16_t a, uint16_t b);

// Test code included
#define __TEST__

// Enable Look Up Table calculation
#define __LUT__

//
// Shift a 128 bit register
//
static void  inline reg_64_2_shift( uint64_t *sr )
{
    sr[0] = (sr[0]<<1) | (sr[1]>>63);
    sr[1] = (sr[1]<<1);
}
//
// Packing routines
// len in is always in bits
// len returned is in bytes
//
static int pack_1_to_8(uint8_t *in, uint8_t *out, int len){
	int d = len/8;
	int r = len%8;
	int idx = 0;
	for( int i = 0; i < d; i++){
		out[i] = in[idx++];
		out[i] <<=1;
		out[i] |= in[idx++];
		out[i] <<=1;
		out[i] |= in[idx++];
		out[i] <<=1;
		out[i] |= in[idx++];
		out[i] <<=1;
		out[i] |= in[idx++];
		out[i] <<=1;
		out[i] |= in[idx++];
		out[i] <<=1;
		out[i] |= in[idx++];
		out[i] <<=1;
		out[i] |= in[idx++];
	}
	if( r == 0 ) return d;
	out[d] = 0;
	uint8_t cnt = 7;
    for( int i = 0; i < r; i++){
    	out[d] |= in[idx++] ? (1<<cnt) : 0;
    	cnt--;
    }
	return (d + 1);
}
//
// Pack 8 to 1
// length in and out is in bits
//
static int pack_8_to_1(uint8_t *in, uint8_t *out, int len){
	int d = len/8;
	int r = len%8;
	int odx = 0;
	for( int i = 0; i < d; i++){
		out[odx++]= in[i] & 0x80 ? 1 : 0;
		out[odx++]= in[i] & 0x40 ? 1 : 0;
		out[odx++]= in[i] & 0x20 ? 1 : 0;
		out[odx++]= in[i] & 0x10 ? 1 : 0;
		out[odx++]= in[i] & 0x08 ? 1 : 0;
		out[odx++]= in[i] & 0x04 ? 1 : 0;
		out[odx++]= in[i] & 0x02 ? 1 : 0;
		out[odx++]= in[i] & 0x01 ? 1 : 0;
	}
	if( r == 0 ) return odx;
    return odx;
	uint8_t cnt = 7;
    for( int i = 0; i < r; i++){
    	out[odx++] = in[d] & (1<<cnt) ? 1 : 0;
    	cnt--;
    }
    return odx;
}
//
// Galois calculations
//
uint16_t m_logtab[0x200];
uint16_t m_alogtab[0x220];
//
// value 0x21 comes from first polynomial 1
//
static uint16_t bch_alpha_power(uint16_t a, uint16_t pwr)
{
	for (int i = 0; i < pwr; i++){
		a <<=1;
		if ( a & GP_SIZE) a ^= m_gmod;
	}
	return a & GP_MASK;
}

static void bch_alog_log_build_table(void){
	m_alogtab[0]     = 0;
	m_alogtab[1]     = 1;
	for( int i = 2; i < (GT_SIZE); i++){
		m_alogtab[i] = bch_alpha_power(m_alogtab[i-1], 1);
	}
	for( int i = 0; i < GP_SIZE; i++){
		m_logtab[m_alogtab[i]] = i;
	}
}

#ifdef __LUT__

// High speed multiply using a large lookup table

static uint16_t m_mult[0x40000];

void build_mult_table(void){
	for( int i = 0; i < 0x40000; i++){
		m_mult[i] = cmult((i>>9),i&0x1FF);
	}
}
#define gmult(a,b) (m_mult[(a<<9)|(b)])

typedef struct{
	uint64_t tab[2];
}BchLut;

BchLut   m_bch_lut[256];

static uint16_t cgmpwr(uint16_t a, uint16_t pwr)
{
	return m_alogtab[m_logtab[a]+pwr];
}
static void  inline reg_64_2_shift8( uint64_t *sr )
{
    sr[0] = (sr[0]<<8) | (sr[1]>>56);
    sr[1] = (sr[1]<<8);
}

static void bch_build_parity_check_lut( void )
{
    uint64_t b;
    uint64_t shift[2];

    for( int n = 0; n <= 255; n++){
        shift[0] = n;
        shift[0] <<= 56;
        shift[1] = 0;
        for( int i = 0; i < 8; i++ )
        {
            b =  (shift[0]>>63)&1;
            reg_64_2_shift( shift );
            if( b )
            {
                shift[0] ^= m_64_poly[0];
                shift[1] ^= m_64_poly[1];
            }
        }
        m_bch_lut[n].tab[0] = shift[0];
        m_bch_lut[n].tab[1] = shift[1]&0xFFFFFFFFFFFFFFFC;
    }
}

//
// Encode 8 bits at a time
//
static void bch_encode_by_8( uint8_t *in, uint64_t *out, int len ){
    uint8_t b;

    for( int i = 0; i < len; i++){
    	b = (out[0]>>56)^in[i];
    	reg_64_2_shift8( out );
        out[0] ^= m_bch_lut[b].tab[0];
        out[1] ^= m_bch_lut[b].tab[1];
    }
}
static void bch_encode_fast( uint8_t *inout, uint64_t *sr, int len ){
    uint8_t b[(BCH_N/8)+1];
    int n = (len/8);
    // Pack the binary bitstream into bytes
    pack_1_to_8(inout, b, len);
	bch_encode_by_8( b, sr, n);
    // final bits
	for( int i = (n*8); i < len; i++){
		b[0] = (sr[0]>>63)^inout[i];
	    reg_64_2_shift( sr );
	    if(b[0]){
	    	sr[0] ^=  m_64_poly[0];
	    	sr[1] ^=  m_64_poly[1];
	    }
	}
}
//
// bitstream input
//
void m17_bch_encode_fast( uint8_t *inout ){
    uint64_t sr[2];
    //Zero the shift register
    sr[0] = 0;
    sr[1] = 0;
    bch_encode_fast( inout, sr, BCH_K );
    // Output the PARITY bits
    for(int i = BCH_K ; i < BCH_N; i++){
   	    inout[i] = (sr[0]>>63);
    	reg_64_2_shift( sr );
    }
}

#endif

#ifndef __LUT__

#define gmult(a,b) (cmult(a,b))

//
// value 0x21 comes generator polynomial 1 reversed
//
static uint16_t cgmpwr(uint16_t a, uint16_t pwr)
{
	uint16_t out;
	out = a;
	for (int i = 0; i < pwr; i++){
		out <<=1;
		if (out & 0x200) out ^= m_gmod;
	}
	return out & 0x1FF;
}
#endif

static uint16_t cmult(uint16_t a, uint16_t b){

	uint16_t sr = 0;
	for (int i = 0; i < BCH_M; i++){
		sr <<= 1;
		if (a  & 0x100)    sr ^= b;
		if (sr & GP_SIZE)  sr ^= m_gmod;//a^10 = (a + 1)
		a <<= 1;
	}
	return (uint16_t)(sr & GP_MASK);
}

static void bch_array_copy(uint16_t *out, uint16_t *in, int l){
	for (int i = 0; i < l; i++) out[i] = in[i];
}

static void bch_array_add(uint16_t *out, uint16_t *ina, uint16_t *inb, int l){
	for (int i = 0; i < l; i++) out[i] = ina[i] ^ inb[i];
}

static void bch_array_mult(uint16_t *out, uint16_t *ina, uint16_t v, int px, int l){
	for (int i = 0; i < (l - px); i++) out[i + px] = gmult(ina[i], v);
}

static void bch_build_poly_inversion_table(void){

	memset(m_pinv, 0, sizeof(uint16_t)*BCH_N);

	for (int i = 1; i <= BCH_N; i++){
		if (m_pinv[i] == 0){
			for (int j = i; j <= BCH_N; j++){
				if (m_pinv[j] == 0){
					if (gmult(i, j) == 0x0001){
						m_pinv[i] = j;
						m_pinv[j] = i;
						break;
					}
				}
			}
		}
	}
}

static void fix_errors(uint8_t *inout, int n, uint16_t *z, int r){
	for( int i = 0; i < r; i++){
		int pos = n - (z[i] + 1);
		if((pos >= 0)&&(pos < n)) inout[pos] ^= 1;
	}
}

static void bch_berk(uint16_t *s, uint16_t *aa )
{
	typedef struct{
		uint16_t ar[BCH_2T+1];
	}tau;

	tau      au_array[BCH_2T+2];
	uint16_t du_array[BCH_2T+1];
	uint16_t hu_array[BCH_2T+1];

	int p    =  0;
	int pv   =  0;
	int pwr  =  0;

	// Zero all the arrays
	memset(au_array, 0, sizeof(tau)      * (BCH_2T+2));
	memset(du_array, 0, sizeof(uint16_t) * (BCH_2T+1));
	memset(hu_array, 0, sizeof(uint16_t) * (BCH_2T+1));

	// C arrays start at 0
	tau      *a  = &au_array[1];
	uint16_t *d  = &du_array[1];
	uint16_t *h  = &hu_array[1];

	// Initial conditions
	int u = -1;

    a[u].ar[0] = 1;
	d[u] = 1;
	h[u] = 0;
    u++;

	a[u].ar[0] = 1;
	d[u] = s[1];
	h[u] = 0;

	for (int row = 1; row < BCH_2T; row++)
	{
		int k = u;

		if (d[k] == 0)
		{
			bch_array_copy(a[k + 1].ar, a[k].ar, BCH_2T+1);
			h[k + 1] = h[k];
		}
		else
		{
			// Find the largest by row
			int pmax = -2;
			for (int r = -1; r < k; r++)
			{
				pv = r - h[r];
				if ((pv > pmax) && (d[r] != 0))
				{
					p    = r;
					pmax = pv;
				}
			}
			// Calculate new au value
			uint16_t v = gmult(d[k], ginv(d[p]));
			pwr = k - p;
			bch_array_mult(a[k + 1].ar, a[p].ar, v, pwr, BCH_2T+1);
			bch_array_add(a[k + 1].ar, a[k + 1].ar, a[k].ar, BCH_2T+1);
			h[k + 1] = (h[u] > (h[p] + k - p)) ? h[k] : (h[p] + k - p);
		}
		if((k+1) < BCH_2T){
			if((k&1)==0){
				d[k+1] = 0;// GF(2) so only need to calculate odd values as d[even] = 0
			}else{
		        int an = 1;
		        d[k + 1] = s[k + 2];
		        for (int sn = k + 1; sn >= (k + 2 - h[k + 1]); sn--,an++)
		        {
		             d[k + 1] = gadd(d[k + 1], gmult(s[sn], a[k + 1].ar[an]));
		        }
			}
		    u++;
		}
	}
	memcpy(aa, a[BCH_2T-1].ar, sizeof(uint16_t)*(BCH_T+1));
}
static int bch_chien_search(uint16_t *a, uint16_t *z )
{
	// Calculate the reciprocal of the coefficients
	int order, nr_coffs, flag;
	static uint16_t  ord[BCH_T+1];
	static uint16_t  t[BCH_T+1];
	order    = 0;
	nr_coffs = 0;
    flag     = 0;

    for (int i = BCH_T; i >= 0; i--)
	{
		if (a[i] != 0)
		{
			if (flag)
			{
				ord[nr_coffs] = order;
				t[nr_coffs]   = a[i];
				nr_coffs++;
			}
			else
			{
				t[0]     = a[i];
				ord[0]   = order;
				flag     = 1;
				order    = 0;
				nr_coffs = 1;
			}
		}
		order++;
	}

    int eq_order = ord[nr_coffs -1];

	//
	// We now have the inverse of sigma, we can do an exhaustive search
	// to find the roots
	//
	int roots = 0;
	uint16_t y[BCH_T+1];
	uint16_t sum;

	// Sigma ^ == 0
	sum = 0;

	for (int m = 0; m < nr_coffs; m++)
	{
		y[m] = t[m];
		sum  = gadd(sum,t[m]);
	}

	if (sum == 0)
	{
		z[roots++] = 0;
		if (roots == eq_order) return roots;
	}

	// sigma ^ > 0

	for (int n = 1; n < BCH_N; n++)
	{
		sum = y[0];
		for (int m = 1; m < nr_coffs; m++)
		{
			y[m] = gmult(y[m], gpwrn(1, ord[m]));
			sum  = gadd(sum, y[m]);
		}
		if (sum == 0)
		{
			z[roots++] = n;
			if (roots == eq_order) return roots;
		}
	}
	// If we get here we have failed to find the roots.
	return -1;
}

//
// Polynomial calculation routines
//
// multiply polynomials
//
static int poly_mult( const int *ina, int lena, const int *inb, int lenb, int *out )
{
    memset( out, 0, sizeof(int)*(lena+lenb));

    for( int i = 0; i < lena; i++ )
    {
        for( int j = 0; j < lenb; j++ )
        {
            if( ina[i]*inb[j] > 0 ) out[i+j]++;// count number of terms for this pwr of x
        }
    }
    int max=0;
    for( int i = 0; i < lena+lenb; i++ )
    {
        out[i] = out[i]&1;// If even ignore the term
        if(out[i]) max = i;
    }
    // return the size of array to house the result.
    return max + 1;

}

//
// Pack the polynomial into a 64 bit array
//

static void poly_64_pack( const int *pin, uint64_t* pout, int len )
{
    int lw = len/64;
    int ptr = 0;
    uint64_t temp;
    if( len % 64 ) lw++;

    for( int i = 0; i < lw; i++ )
    {
        temp    = 0x8000000000000000;
        pout[i] = 0;
        for( int j = 0; j < 64; j++ )
        {
            if( pin[ptr++] ) pout[i] |= temp;
            temp >>= 1;
        }
    }
}
//
// Used to pack the modulo value used in the gmult
//
static uint16_t poly_16_pack( const int *pin, int len )
{
	len = len - 1;// Arrays start at zero!
	uint16_t sr = 0;
	if(len > 15) len = 15;
	for( int i = len; i >= 0; i--){
		sr <<= 1;
		sr |= pin[i] ? 1 : 0;
	}
	return sr;
}

static void poly_reverse( int *pin, int *pout, int len )
{
    int c;
    c = len-1;

    for( int i = 0; i < len; i++ )
    {
        pout[c--] = pin[i];
    }
}

static void bch_encode(uint8_t *in, uint64_t *sr, int len ){
    uint8_t b;

    for( int i = 0; i < len; i++){
    	b = (sr[0]>>63)^in[i];
        sr[0] = (sr[0]<<1) | (sr[1]>>63);
        sr[1] = (sr[1]<<1);
    	if(b){
    		sr[0] ^=  m_64_poly[0];
    		sr[1] ^=  m_64_poly[1];
    	}
    }
}

/////////////////////////////////////////////////////////////////////////////
//
// Externally visible
//
/////////////////////////////////////////////////////////////////////////////
static bool m17_bch_check( uint8_t *in ){
    uint64_t sr[2];
    //Zero the shift register
    sr[0] = 0;
    sr[1] = 0;

#ifdef __LUT__
    bch_encode_fast( in, sr, BCH_N );
#else
    bch_encode(  in, sr, BCH_N  );
#endif
    if(sr[0] != 0) return false;
    if(sr[1] != 0) return false;
    return true;
}

void m17_bch_encode( uint8_t *inout ){
    uint64_t sr[2];
    //Zero the shift register
    sr[0] = 0;
    sr[1] = 0;
    bch_encode(inout, sr, BCH_K );
    // Output the PARITY bits
    for(int i = BCH_K; i < BCH_N; i++){
   	    inout[i] = ((sr[0]>>63));
    	reg_64_2_shift( sr );
    }
}

int m17_bch_decode( uint8_t *inout ){
	static uint16_t s[BCH_2T+1];
	static uint16_t z[BCH_2T+2];
	static uint16_t a[BCH_T+1];
	int r = 0;

	memset(s,0,sizeof(uint16_t)*(BCH_2T+1));
	memset(z,0,sizeof(uint16_t)*(BCH_2T+2));


    if(m17_bch_check( inout )==false){
    	// Block is in error
   		// Calculate the syndromes
   		s[0]  = 1;
   		for(int i = 0; i < BCH_N; i++){
   		    s[1]  = s[1]  ? gpwrn(s[1],1)   ^ inout[i] : inout[i];
   		    s[3]  = s[3]  ? gpwrn(s[3],3)   ^ inout[i] : inout[i];
   		    s[5]  = s[5]  ? gpwrn(s[5],5)   ^ inout[i] : inout[i];
   		    s[7]  = s[7]  ? gpwrn(s[7],7)   ^ inout[i] : inout[i];
   		    s[9]  = s[9]  ? gpwrn(s[9],9)   ^ inout[i] : inout[i];
   		    s[11] = s[11] ? gpwrn(s[11],11) ^ inout[i] : inout[i];
   		    s[13] = s[13] ? gpwrn(s[13],13) ^ inout[i] : inout[i];
   		    s[15] = s[15] ? gpwrn(s[15],15) ^ inout[i] : inout[i];
   		    s[17] = s[17] ? gpwrn(s[17],17) ^ inout[i] : inout[i];
   		    s[19] = s[19] ? gpwrn(s[19],19) ^ inout[i] : inout[i];
   		    s[21] = s[21] ? gpwrn(s[21],21) ^ inout[i] : inout[i];
   		    s[23] = s[23] ? gpwrn(s[23],23) ^ inout[i] : inout[i];
   		    s[25] = s[25] ? gpwrn(s[25],25) ^ inout[i] : inout[i];
   		    s[27] = s[27] ? gpwrn(s[27],27) ^ inout[i] : inout[i];
  		}
   		s[2]  = gmult(s[1],  s[1]);
   		s[4]  = gmult(s[2],  s[2]);
   		s[6]  = gmult(s[3],  s[3]);
   		s[8]  = gmult(s[4],  s[4]);
   		s[10] = gmult(s[5],  s[5]);
		s[12] = gmult(s[6],  s[6]);
		s[14] = gmult(s[7],  s[7]);
		s[16] = gmult(s[8],  s[8]);
		s[18] = gmult(s[9],  s[9]);
		s[20] = gmult(s[10], s[10]);
		s[22] = gmult(s[11], s[11]);
		s[24] = gmult(s[12], s[12]);
		s[26] = gmult(s[13], s[13]);
		s[28] = gmult(s[14], s[14]);

		bch_berk( s, a );
		r = bch_chien_search( a, z );
		if( r > 0 ) fix_errors(inout, BCH_N, z, r);
    }
    return r;
}
void m17_bch_init(void){

	// Base Polynomials

    int poly01[10]={1,0,0,0,0,1,0,0,0,1};
    int poly02[10]={1,0,0,1,0,1,1,0,0,1};
    int poly03[10]={1,1,0,0,1,1,0,0,0,1};
    int poly04[10]={1,0,1,0,0,1,1,0,0,1};
    int poly05[10]={1,1,0,0,0,1,0,0,1,1};
    int poly06[10]={1,0,0,0,1,0,1,1,0,1};
    int poly07[10]={1,0,0,1,1,1,0,1,1,1};
    int poly08[10]={1,1,0,1,1,0,0,0,0,1};
    int poly09[10]={1,0,1,1,0,1,1,0,1,1};
    int poly10[10]={1,1,1,0,0,0,0,1,0,1};
    int poly11[10]={1,0,0,0,0,1,0,1,1,1};
    int poly12[10]={1,1,1,1,1,0,1,0,0,1};
    int poly13[10]={1,1,1,1,1,0,0,0,1,1};
    int poly14[10]={1,1,1,0,0,0,1,1,1,1};

    // Multiply them together
    int len;
    int polyout[2][200];

    memset(polyout[0],0,sizeof(int)*200);
    memset(polyout[1],0,sizeof(int)*200);

    len = poly_mult( poly01, 10, poly02,     10,  polyout[0] );
    len = poly_mult( poly03, 10, polyout[0], len, polyout[1] );
    len = poly_mult( poly04, 10, polyout[1], len, polyout[0] );
    len = poly_mult( poly05, 10, polyout[0], len, polyout[1] );
    len = poly_mult( poly06, 10, polyout[1], len, polyout[0] );
    len = poly_mult( poly07, 10, polyout[0], len, polyout[1] );
    len = poly_mult( poly08, 10, polyout[1], len, polyout[0] );
    len = poly_mult( poly09, 10, polyout[0], len, polyout[1] );
    len = poly_mult( poly10, 10, polyout[1], len, polyout[0] );
    len = poly_mult( poly11, 10, polyout[0], len, polyout[1] );
    len = poly_mult( poly12, 10, polyout[1], len, polyout[0] );
    len = poly_mult( poly13, 10, polyout[0], len, polyout[1] );
    len = poly_mult( poly14, 10, polyout[1], len, polyout[0] );


    len = BCH_NK;
    m_gmod = poly_16_pack( poly01, BCH_M );
#ifdef __LUT__
    build_mult_table();
#endif

    poly_reverse( polyout[0], polyout[1], len );
    poly_64_pack( polyout[1], m_64_poly,  len );
    bch_build_poly_inversion_table();
    bch_alog_log_build_table();
#ifdef __LUT__
    bch_build_parity_check_lut();
#endif

}
//
// Test harness
//

#ifdef __TEST__

bool decode_test(uint8_t *bits){
    m17_bch_decode( bits );
    return m17_bch_check( bits );
}

bool bch_test(int n){

    // Now do a test
    static uint8_t bits[BCH_N];

    for(int i = 0; i < BCH_K; i++){
    	bits[i] = rand()&1;
    }

    m17_bch_encode( bits );

    // Add some errors
    for( int i = 0; i < n; i++){
    	bits[rand()%511] ^= 1;
    }

   	if(decode_test(bits) == false){
        printf("BCH Correction FAIL\n");
        return false;
   	}
   	return true;
}

uint64_t GetTimeStamp(void) {
    struct timeval tv;
    gettimeofday(&tv,NULL);
    return tv.tv_sec*(uint64_t)1000000+tv.tv_usec;
}

void test(int m){
    //
	// Test example code below here
	//
	int   fails = 0;
    int   n     = 100000;
    float d     = 100.0/n;


    uint64_t s,e;

    s = GetTimeStamp();

    printf("Start of BCH test %d errors per frame\n",m);
	for( int i = 0; i < n; i++ ){
		if(bch_test(m)== false) fails++;;
	}
	printf("Number Failed codewords %d, percentage failure %.2f\n",fails,fails*d);
    e = GetTimeStamp();

    float du = (e - s)/1000000.0;

    printf("Duration of test %.2f secs\n",du);
    printf("Number of 511 bit codewords received %d\n",n);
    printf("Equivalent bitrate %.2f Mbs\n", (n*BCH_K)/(du*1000000.0));

}
#endif
/*
 *
 * To use this program you will need to call m17_bch_init() first
 * Then multiple calls of m17_bch_encode() and m17_bch_decode()
 *
 * The array passed to these functions is a read / write uint8_t array with the data
 * encoded as 1 bit per byte. The arrays are BCH_N bits long.
 *
 * To encode a word you pass an array with BCH_K bits of the data to encode
 * it returns the array with the parity bits written in the BCH_K to BCH_N entries.
 *
 * To decode you pass the BCN_N bits of the received word into the bch_decode function
 * it returns the corrected bits in the first BCH_K entries of the array
 *
 * There is also a final function called bch_check() you pass the BCH_N bits
 * of the codeword to it and it returns a true / false value depending on
 * whether is considers the codeword to be valid.
 *
 * The program only runs error correction if the codeword you pass to it is in error.
 * So the decode speed is not constant and depends on number of errors
 * It is capable of recovering up to 14 bit errors.
 *
 * the __TEST__ define includes the test harness code
 * the __LUT__  define uses large lookup tables and is about 40% faster
 *
 * When running the program from the command line you can pass a number
 * between 0 and 14 telling the program how many error bits you want in each codeword
 *
 *
 */
int main(int argc, char **argv ){
	m17_bch_init();

#ifdef __TEST__
	int m = 14;
    if(argc == 2) m = atoi(argv[1]);
    if( m < 0 ) m = 0;
    if(m > 14)  m = 14;
    test(m);
#endif

}

