/* Exhaustive check of the Diamond–Yehudayoff conjecture over ALL real weights for small d.
 * Enumerates every affinely closed S ⊆ {0,1}^{2d} with aff(S) ∩ cube ⊆ D_d (no pair i with x_i = y_i = 1)
 * and reports max |S|. Affine rank is computed modulo two primes (ranks of small 0/±1 integer vectors over
 * Q equal those mod p unless p divides certain minors; agreement mod two 61-bit-scale primes is checked).
 * Closed sets are stored in a hash set (256-bit masks for d ≤ 4). usage: dy_affine d */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static const uint64_t P1 = 2305843009213693951ULL; /* 2^61-1 */
static const uint64_t P2 = 4611686018427387847ULL; /* prime < 2^62 */
static uint64_t mulm(uint64_t a, uint64_t b, uint64_t p){ return (uint64_t)((u128)a*b % p); }
static uint64_t powm(uint64_t a, uint64_t e, uint64_t p){ uint64_t r=1; while(e){ if(e&1) r=mulm(r,a,p); a=mulm(a,a,p); e>>=1;} return r; }
static int d, n, NP;
typedef struct { uint64_t w[4]; } Set;   /* up to 256 points */
static inline int has(const Set*s,int p){ return s->w[p>>6]>>(p&63)&1; }
static inline void add(Set*s,int p){ s->w[p>>6]|=1ULL<<(p&63); }
static int isD(int p){ int x=p&((1<<d)-1), y=p>>d; return !(x&y); }
/* basis mod prime in reduced row echelon form; returns rank */
typedef struct { int r; uint64_t v[16][16]; int piv[16]; } Basis;
static int reduce(const Basis*B, uint64_t *v, uint64_t p){ /* reduce v by B; return 1 if nonzero */
  for(int i=0;i<B->r;i++){ int c=B->piv[i]; if(v[c]){ uint64_t f=v[c]; for(int j=0;j<n;j++){ v[j]=(v[j]+p-mulm(f,B->v[i][j],p))%p; } } }
  for(int j=0;j<n;j++) if(v[j]) return 1; return 0; }
static void insert(Basis*B, uint64_t *v, uint64_t p){ int c=0; while(!v[c]) c++; uint64_t inv=powm(v[c],p-2,p);
  for(int j=0;j<n;j++) v[j]=mulm(v[j],inv,p);
  for(int i=0;i<B->r;i++){ uint64_t f=B->v[i][c]; if(f) for(int j=0;j<n;j++) B->v[i][j]=(B->v[i][j]+p-mulm(f,v[j],p))%p; }
  memcpy(B->v[B->r],v,sizeof(uint64_t)*n); B->piv[B->r]=c; B->r++; }
static void vecdiff(int a,int b,uint64_t *v,uint64_t p){ for(int j=0;j<n;j++){ int x=(a>>j&1)-(b>>j&1); v[j]= x>=0? (uint64_t)x : p-1; } }
/* closure of a point list: returns set and dim; checks agreement of both primes */
static Set closure(int *pts,int k,int *dim){
  Basis B1,B2; B1.r=B2.r=0; uint64_t v[16];
  for(int i=1;i<k;i++){ vecdiff(pts[i],pts[0],v,P1); if(reduce(&B1,v,P1)) insert(&B1,v,P1);
                        vecdiff(pts[i],pts[0],v,P2); if(reduce(&B2,v,P2)) insert(&B2,v,P2); }
  if(B1.r!=B2.r){ fprintf(stderr,"prime disagreement\n"); exit(1); }
  Set s; memset(&s,0,sizeof s);
  for(int p=0;p<NP;p++){ vecdiff(p,pts[0],v,P1); int in1=!reduce(&B1,v,P1); vecdiff(p,pts[0],v,P2); int in2=!reduce(&B2,v,P2);
    if(in1!=in2){ fprintf(stderr,"membership disagreement\n"); exit(1);} if(in1) add(&s,p); }
  *dim=B1.r; return s; }
/* hash set of Sets */
static Set *tab; static char *used; static size_t cap, cnt;
static uint64_t hsh(const Set*s){ uint64_t h=1469598103934665603ULL; for(int i=0;i<4;i++){ h^=s->w[i]; h*=1099511628211ULL; h^=h>>29; } return h; }
static int insert_set(const Set*s){ size_t i=hsh(s)&(cap-1); while(used[i]){ if(!memcmp(&tab[i],s,sizeof *s)) return 0; i=(i+1)&(cap-1);} used[i]=1; tab[i]=*s; cnt++; return 1; }
int main(int argc,char**argv){ d=atoi(argv[1]); n=2*d; NP=1<<n; cap=1ULL<<26; tab=malloc(sizeof(Set)*cap); used=calloc(cap,1);
  Set *stack=malloc(sizeof(Set)*(1<<26)); size_t sp=0; int best=0, bestdim=0; long contained=0;
  for(int p=0;p<NP;p++) if(isD(p)){ Set s; memset(&s,0,sizeof s); add(&s,p); if(insert_set(&s)) stack[sp++]=s; }
  int pts[256];
  while(sp){ Set S=stack[--sp]; int k=0; for(int p=0;p<NP;p++) if(has(&S,p)) pts[k++]=p;
    contained++; if(k>best){ best=k; int dm; closure(pts,k,&dm); bestdim=dm; }
    for(int p=0;p<NP;p++){ if(!isD(p)||has(&S,p)) continue; pts[k]=p; int dm; Set T=closure(pts,k+1,&dm);
      int ok=1; for(int q=0;q<NP&&ok;q++) if(has(&T,q)&&!isD(q)) ok=0;
      if(!ok) continue; if(insert_set(&T)) stack[sp++]=T; } }
  printf("d=%d: %ld contained affinely closed sets; max |S| = %d (2^d = %d), extremal affine dim %d\n",d,contained,best,1<<d,bestdim);
}
