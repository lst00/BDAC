#include <assert.h>
#include <time.h>
#include "miracl_core_c_bn254/pair_BN254.h"
#include "miracl_core_c_bn254/big_256_56.h"

typedef ECP_BN254 ECP;
typedef ECP2_BN254 ECP2;
typedef FP12_BN254 FP12;
typedef BIG_256_56 BIG;
#define ell 15
//这一版是使用堆内存
/* public parameters */
typedef struct
{
    ECP P;
    ECP2 Phat;
    BIG r;
} PP_t;

typedef struct
{
    ECP *Psc;        // size: ell * 2
    ECP2 *Phatsc;    // size: ell
} ctx;

typedef struct {
    ECP2 *pk;        // size: ell
    BIG *sk;         // size: ell
    ECP2 *msg_ecp2;  // size: ell
    ECP **mgs_ecp;   // size: ell x (ell + 1)
} usergen;

typedef struct {
    ECP2 *r_ecp2;    // size: ell
    ECP **r_ecp;     // size: ell x (ell + 1)
} matrix_R;

typedef struct
{
    ECP Z;
    ECP Y;
    ECP2 Yhat;
} sigma_t;

void SCGen(PP_t *PP, csprng *rng, ctx *PPxa)
{
    // initialize rng
    char pr[10];
    for (int i = 1; i < 10; i++)
        pr[i] = (char)rand();
    RAND_seed(rng, 10, pr);

    // initialize scheme public parameters
    ECP2_BN254_generator(&PP->Phat);
    ECP_BN254_generator(&PP->P);
    BIG_256_56_rcopy(PP->r, CURVE_Order_BN254);

    BIG a;
    ECP tmp1;
    ECP2 tmp2;
    // initialize ppxa
    // a ← Zp
    BIG_256_56_randomnum(a, PP->r, rng);
    ECP_BN254_copy(&tmp1, &PP->P);
    ECP2_BN254_copy(&tmp2, &PP->Phat);

    // Allocate memory for arrays
    PPxa->Psc = (ECP *)malloc(ell * 2 * sizeof(ECP));
    PPxa->Phatsc = (ECP2 *)malloc(ell * sizeof(ECP2));

    for (int i = 0; i < ell * 2; i++) {
        // Psc[i] = aP,a^2*P....a^2ell**P
        ECP_BN254_mul(&tmp1, a);
        ECP_BN254_copy(&PPxa->Psc[i], &tmp1);
    }

    for (int i = 0; i < ell ; i++) {
        ECP2_BN254_mul(&tmp2, a); // aPhat,..a^ell*Phat
        ECP2_BN254_copy(&PPxa->Phatsc[i], &tmp2);   
    }
}

usergen* KeyGen(PP_t *PP, csprng *rng, ctx *PPxa, int start_n)
{
    usergen *user = (usergen *)malloc(sizeof(usergen));
    
    // Allocate arrays
    user->sk = (BIG *)malloc(ell * sizeof(BIG));
    user->pk = (ECP2 *)malloc(ell * sizeof(ECP2));
    user->msg_ecp2 = (ECP2 *)malloc(ell * sizeof(ECP2));
    user->mgs_ecp = (ECP **)malloc(ell * sizeof(ECP *));
    for (int i = 0; i < ell; i++) {
        user->mgs_ecp[i] = (ECP *)malloc((ell + 1) * sizeof(ECP));
    }

    for (int i = 0; i < ell; i++) {
        BIG x;
        ECP2 w;
        // x ← Zp
        BIG_256_56_randomnum(x, PP->r, rng);
        BIG_256_56_copy(user->sk[i], x);

        // w = x * phat
        ECP2_BN254_copy(&w, &PP->Phat);
        ECP2_BN254_mul(&w, x);
        ECP2_BN254_copy(&user->pk[i], &w);
    }

    for(int i = 0; i < ell; i++) {
        ECP2_BN254_copy(&user->msg_ecp2[i], &user->pk[i]);
    
        int n = start_n;
        for (int j = 0; j < ell + 1; j++) {
            if (n == ell) {
                ECP_BN254_inf(&user->mgs_ecp[i][j]);
            } else {
                ECP_BN254_copy(&user->mgs_ecp[i][j], &PPxa->Psc[n]);
                ECP_BN254_mul(&user->mgs_ecp[i][j], user->sk[i]);
            }
            n++;
        }
    }

    return user;
}

matrix_R* RGEN(usergen **users, int k)
{
    matrix_R *R = (matrix_R *)malloc(sizeof(matrix_R));
    
    // Allocate arrays
    R->r_ecp2 = (ECP2 *)malloc(ell * sizeof(ECP2));
    R->r_ecp = (ECP **)malloc(ell * sizeof(ECP *));
    for (int i = 0; i < ell; i++) {
        R->r_ecp[i] = (ECP *)malloc((ell + 1) * sizeof(ECP));
    }

    for(int i = 0; i < ell; i++) {
        ECP2_BN254_copy(&R->r_ecp2[i], &users[i]->msg_ecp2[k]);

        for (int j = 0; j < ell + 1; j++) {
            ECP_BN254_copy(&R->r_ecp[i][j], &users[i]->mgs_ecp[k][j]);
        }
    }

    return R;
}

bool Verify(ctx *PPxa, PP_t *PP, ECP *commit_j, ECP *prove_i, usergen *user, int id)
{
    ECP commit_all, p;
    int idx = ell + 1 - id;
    
    ECP_BN254_inf(&commit_all);
    for (int i = 0; i < ell; i++) {
        ECP_BN254_add(&commit_all, &commit_j[i]);
    }

    ECP_BN254_inf(&p);
    for (int j = 0; j < ell; j++) {
        ECP_BN254_add(&p, &user->mgs_ecp[j][0]);
    }

    FP12 left, right;
    PAIR_BN254_ate(&left, &PPxa->Phatsc[idx-1], &commit_all);
    PAIR_BN254_fexp(&left);

    PAIR_BN254_double_ate(&right, &PP->Phat, prove_i, &PPxa->Phatsc[idx-1], &p);
    PAIR_BN254_fexp(&right);

    return FP12_BN254_equals(&right, &left);
}

void Sign(PP_t *PP, BIG *sk, ECP *commit_j, sigma_t *sigma, csprng *rng)
{
    BIG y, y_inv;
    ECP factor;
    BIG_256_56_randomnum(y, PP->r, rng);
    BIG_256_56_invmodp(y_inv, y, PP->r);

    ECP_BN254_inf(&(sigma->Z));

    for(int i = 0; i < ell; i++) {
        ECP_BN254_copy(&factor, &commit_j[i]);
        ECP_BN254_mul(&factor, sk[i]);
        ECP_BN254_add(&(sigma->Z), &factor);
    }
    ECP_BN254_mul(&(sigma->Z), y);

    ECP_BN254_copy(&(sigma->Y), &PP->P);
    ECP2_BN254_copy(&(sigma->Yhat), &PP->Phat);
    ECP_BN254_mul(&(sigma->Y), y_inv);
    ECP2_BN254_mul(&(sigma->Yhat), y_inv);
}

bool Versig(PP_t *PP, ECP2 *pk, ECP *commit_j, sigma_t *sigma)
{
    FP12 result, q2, q3, q4, factor;
    PAIR_BN254_ate(&result, &pk[0], &commit_j[0]);
    PAIR_BN254_fexp(&result);
    
    for (int i = 1; i < ell; i++) {
        PAIR_BN254_ate(&factor, &pk[i], &commit_j[i]);
        PAIR_BN254_fexp(&factor);
        FP12_BN254_mul(&result, &factor);
    }
    
    PAIR_BN254_ate(&q2, &(sigma->Yhat), &(sigma->Z));
    PAIR_BN254_fexp(&q2);

    PAIR_BN254_ate(&q3, &PP->Phat, &(sigma->Y));
    PAIR_BN254_fexp(&q3);
    PAIR_BN254_ate(&q4, &(sigma->Yhat), &PP->P);
    PAIR_BN254_fexp(&q4);

    return (bool)FP12_BN254_equals(&result, &q2) && (bool)FP12_BN254_equals(&q3, &q4);
}

// Memory freeing functions
void free_ctx(ctx *PPxa)
{
    if (PPxa->Psc) free(PPxa->Psc);
    if (PPxa->Phatsc) free(PPxa->Phatsc);
}

void free_usergen(usergen *user)
{
    if (user) {
        if (user->sk) free(user->sk);
        if (user->pk) free(user->pk);
        if (user->msg_ecp2) free(user->msg_ecp2);
        if (user->mgs_ecp) {
            for (int i = 0; i < ell; i++) {
                if (user->mgs_ecp[i]) free(user->mgs_ecp[i]);
            }
            free(user->mgs_ecp);
        }
        free(user);
    }
}

void free_matrix_R(matrix_R *R)
{
    if (R) {
        if (R->r_ecp2) free(R->r_ecp2);
        if (R->r_ecp) {
            for (int i = 0; i < ell; i++) {
                if (R->r_ecp[i]) free(R->r_ecp[i]);
            }
            free(R->r_ecp);
        }
        free(R);
    }
}

int main()
{
    ctx PPxa;
    csprng RNG;
    PP_t PP;
    SCGen(&PP, &RNG, &PPxa);
    
    clock_t start, step0, step1, end;
    double cpu_time_used, verified_time_used;

    // Allocate users array
    usergen **users = (usergen **)malloc(ell * sizeof(usergen *));
    int start_n = 0;
    for (int i = 0; i < ell; i++) {
        users[i] = KeyGen(&PP, &RNG, &PPxa, start_n);
        start_n++;
    }

    start = clock();
    
    // Allocate R array
    matrix_R **R = (matrix_R **)malloc(ell * sizeof(matrix_R *));
    for (int k = 0; k < ell; k++) {
        R[k] = RGEN(users, k);
    }

    // Allocate r array
    BIG *r = (BIG *)malloc(ell * sizeof(BIG));
    for (int i = 0; i < ell; i++) {
        BIG r_j;
        BIG_256_56_randomnum(r_j, PP.r, &RNG);
        BIG_256_56_copy(r[i], r_j);
    }

    // Allocate commit_j array
    ECP *commit_j = (ECP *)malloc(ell * sizeof(ECP));
    for(int i = 0; i < ell; i++) {
        ECP_BN254_copy(&commit_j[i], &PP.P);
        ECP_BN254_mul(&commit_j[i], r[i]);
        for (int j = 0; j < ell; j++) {
            ECP_BN254_add(&commit_j[i], &R[i]->r_ecp[j][0]);
        }
    }

    // Allocate prove_j array
    ECP *prove_j = (ECP *)malloc(ell * sizeof(ECP));
    int id = 1;
    int idx = ell + 1 - id; 
    
    for(int i = 0; i < ell; i++) {
        ECP_BN254_copy(&prove_j[i], &PPxa.Psc[idx - 1]);
        ECP_BN254_mul(&prove_j[i], r[i]); 
        for (int j = 0; j < ell; j++) {
            ECP_BN254_add(&prove_j[i], &R[i]->r_ecp[j][idx]);
        } 
    }

    ECP prove_i;
    ECP_BN254_inf(&prove_i);
    for(int i = 0; i < ell; i++) {
        ECP_BN254_add(&prove_i, &prove_j[i]);
    }

    sigma_t sigma;
    Sign(&PP, users[0]->sk, commit_j, &sigma, &RNG);

    end = clock();
    cpu_time_used = ((double)(end - start)) / CLOCKS_PER_SEC;
    printf("cpu_time_used: %f s\n", cpu_time_used);

    step0 = clock();
    bool valid = Verify(&PPxa, &PP, commit_j, &prove_i, users[id - 1], id);
    bool valid2 = Versig(&PP, users[id - 1]->pk, commit_j, &sigma);
    
    
    if (valid && valid2) {
        printf("Verification successfully!\n");
    } else {
        printf("Verification failed \n");
    }
    
    step1 = clock();
    verified_time_used = ((double)(step1 - step0)) / CLOCKS_PER_SEC;
    printf("verified_time_used: %f s\n", verified_time_used);

    // Free allocated memory
    free(r);
    free(commit_j);
    free(prove_j);
    
    for (int i = 0; i < ell; i++) {
        free_matrix_R(R[i]);
        free_usergen(users[i]);
    }
    free(R);
    free(users);
    free_ctx(&PPxa);

    return 0;
}