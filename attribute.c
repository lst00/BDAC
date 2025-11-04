/*
#include <assert.h>
#include <time.h>
#include "miracl_core_c_bn254/pair_BN254.h"
#include "miracl_core_c_bn254/big_256_56.h"

typedef ECP_BN254 ECP;
typedef ECP2_BN254 ECP2;
typedef FP12_BN254 FP12;
typedef BIG_256_56 BIG;

#define ell 4096
static int count =5;


typedef struct
{
    ECP P;
    ECP2 Phat;
    BIG r;
} PP_t;

typedef struct
{
    ECP Psc[ell + 1];
    ECP2 Phatsc[ell + 1];
} ctx;



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

    for (int i = 0; i < ell + 1 ; i++) {
        // Psc[i] = a^i * P
        ECP_BN254_copy(&PPxa->Psc[i], &tmp1);
        ECP_BN254_mul(&tmp1, a);  // tmp1 = a^(i+1) * P for next round
        // printf("psc[%d] = \n ",i);ECP_BN254_output(&PPxa->Psc[i]);
        // Phatsc[i] = a^i * Phat
        ECP2_BN254_copy(&PPxa->Phatsc[i], &tmp2);
        ECP2_BN254_mul(&tmp2, a); // tmp2 = a^(i+1) * Phat for next round
        // printf("phat[%d] = \n ",i);ECP2_BN254_output(&PPxa->Phatsc[i]);
    }

}

void attriGen(PP_t *PP,ctx *PPxa, BIG *attri ,ECP *result)
{

    BIG F[ell + 1];// 展开后最大长度为 ell+1
    BIG temp[ell + 1];
    BIG zero, one, p;

    BIG_256_56_zero(zero);
    BIG_256_56_one(one);
    BIG_256_56_copy(p, PP->r);

    // 初始化 f(x) = 1
    BIG_256_56_copy(F[0], one);
    for (int i = 1; i <= ell; i++) {
        BIG_256_56_zero(F[i]);
        BIG_256_56_zero(temp[i]);
    }

    // 多项式乘法迭代
    for (int i = 0; i < ell; i++) {
        // temp[j] = F[j]
        for (int j = 0; j <= ell; j++) {
            BIG_256_56_copy(temp[j], F[j]);
        }

        for (int j = 0; j <= i + 1; j++) {
            BIG t1, t2;
            BIG_256_56_zero(t1);
            BIG_256_56_zero(t2);

            if (j <= i) {
                BIG_256_56_modmul(t1, temp[j], attri[i], p);   // t1 = temp[j] * attri[i]
                BIG_256_56_sub(t1, p, t1);              // t1 = -temp[j]*attri[i]
                BIG_256_56_mod(t1, p);                  // 保证 t1 ∈ Zp
            }

            if (j > 0) {
                BIG_256_56_copy(t2, temp[j - 1]);          // t2 = temp[j-1]
            }
            BIG_256_56_add(F[j], t1, t2);                  // F[j] = -attri[i]*N[j] + F[j-1]
            BIG_256_56_mod(F[j], p);                    // F[j] ∈ Zp
        }
        
    }


    ECP_BN254_inf(result);

    for (int i = 0; i <= ell; i++) {
        ECP tempP ;
        BIG_256_56 scalar ;
        // scalar = F[i] mod r（可省略，因为F[i]已经是Zp中）
        BIG_256_56_copy(scalar, F[i]);
        // tempP = scalar * Psc[i]
        ECP_BN254_copy(&tempP, &PPxa->Psc[i]);
        ECP_BN254_mul(&tempP, scalar); 
        // result += tempP
        ECP_BN254_add(result, &tempP);
        }
      
}; 

void GxGen(PP_t *PP, ctx *PPxa, BIG *attri, ECP *result ,int count) 
{
    BIG G[count + 1];// 展开后最大长度为 ell+1
    BIG temp[count + 1];
    BIG zero, one, p;

    BIG_256_56_zero(zero);
    BIG_256_56_one(one);
    BIG_256_56_copy(p, PP->r);

    // 初始化 f(x) = 1
    BIG_256_56_copy(G[0], one);
    for (int i = 1; i <= count; i++) {
        BIG_256_56_zero(G[i]);
        BIG_256_56_zero(temp[i]);
    }

    // 多项式乘法迭代
    for (int i = 0; i < count; i++) {
        // temp[j] = F[j]
       //  printf("G[%d] = ", i);BIG_256_56_output(attri[i]);printf("\n");
        for (int j = 0; j <= count ; j++) {
            BIG_256_56_copy(temp[j], G[j]);
        }

        for (int j = 0; j <= i + 1; j++) {
            BIG t1, t2;
            BIG_256_56_zero(t1);
            BIG_256_56_zero(t2);

            if (j <= i) {
                BIG_256_56_modmul(t1, temp[j], attri[i], p);  // t1 = temp[j] * attri[i]
                BIG_256_56_modneg(t1, t1, p);
                
            }

            if (j > 0) {
                BIG_256_56_copy(t2, temp[j - 1]);          // t2 = temp[j-1]
            }
            BIG_256_56_add(G[j], t1, t2);                  // F[j] = -attri[i]*N[j] + F[j-1]
            BIG_256_56_mod(G[j], p);                    // F[j] ∈ Zp

        }

    }

    // 初始化结果点
    ECP_BN254_inf(result);

    // result = ∑ F[i] * Psc[i]
    for (int i = 0; i <= count ; i++) {
        ECP tempP;
        BIG scalar;
        BIG_256_56_copy(scalar, G[i]);
        ECP_BN254_copy(&tempP, &PPxa->Psc[i]);
        ECP_BN254_mul(&tempP, scalar);
        ECP_BN254_add(result, &tempP);
    }

}

void HxGen(PP_t *PP, ctx *PPxa, BIG *attri, ECP2 *result ,int count)
{
    BIG H[count + 1];// 展开后最大长度为 ell+1
    BIG temp[count + 1];
    BIG zero, one, p;

    BIG_256_56_zero(zero);
    BIG_256_56_one(one);
    BIG_256_56_copy(p, PP->r);

    // 初始化 f(x) = 1

    BIG_256_56_copy(H[0], one);

    for (int i = 1; i <= count; i++) {
        BIG_256_56_zero(H[i]);
        BIG_256_56_zero(temp[i]);
    }

    // 多项式乘法迭代
    for (int i = 0; i < count ; i++) {
        // temp[j] = F[j]
        for (int j = 0; j <= count ; j++) {
            BIG_256_56_copy(temp[j], H[j]);
        }

        for (int j = 0; j <= i + 1; j++) {
            BIG t1, t2;
            BIG_256_56_zero(t1);
            BIG_256_56_zero(t2);

            if (j <= i) {
                BIG_256_56_modmul(t1, temp[j], attri[i], p);   // t1 = temp[j] * attri[i]
                BIG_256_56_modneg(t1, t1, p);
            }

            if (j > 0) {
                BIG_256_56_copy(t2, temp[j - 1]);          // t2 = temp[j-1]
            }
            BIG_256_56_add(H[j], t1, t2);                  // F[j] = -attri[i]*N[j] + F[j-1]
            BIG_256_56_mod(H[j], p);                    // F[j] ∈ Zp
        }
        
    }

    // 初始化结果点
    ECP2_BN254_inf(result);

    // result = ∑ F[i] * Psc[i]
   for (int i = 0; i <= count ; i++) {
        ECP2 tempP;
        BIG scalar;

        BIG_256_56_copy(scalar, H[i]);
        ECP2_BN254_copy(&tempP, &PPxa->Phatsc[i]);
        ECP2_BN254_mul(&tempP, scalar);
        ECP2_BN254_add(result, &tempP);
    }
 


}
int main()
{

    clock_t start, end , start1,end1;
    double cpu_time_used,step_time_used;
    
    ctx PPxa;
    csprng RNG;
    PP_t PP;
    SCGen(&PP,&RNG,&PPxa);

    
    ECP result;
    ECP resultG;
    ECP2 resultest;
    ECP2 resultH;
    BIG attri[ell];
    BIG attriH[count];
    BIG attriG[ell - count];
 
    for (int i = 0; i < ell; i++)
    {
        BIG m;
        //  b ← Zp
        BIG_256_56_randomnum(m, PP.r, &RNG);
        BIG_256_56_copy(attri[i], m);
    }

    for (int i = 0; i < ell - count; i++)
    {
        BIG_256_56_copy(attriG[i], attri[i]);
    }
 
    for (int i = 0; i < count; i++)
    {
        BIG_256_56_copy(attriH[i], attri[ ell - count + i]);
    }

    start = clock();
    attriGen(&PP,&PPxa, attri, &result);

    end = clock();
    step_time_used = ((double)(end - start)) / CLOCKS_PER_SEC;
    printf("step_time_used: %f s\n", step_time_used);



    start1 = clock();
    GxGen(&PP,&PPxa, attriG, &resultG, ell - count );
    HxGen(&PP,&PPxa, attriH, &resultH, count );

    FP12 left, right;
    PAIR_BN254_ate(&left, &PP.Phat, &result);
    PAIR_BN254_fexp(&left);

    PAIR_BN254_ate(&right, &resultH, &resultG);
    PAIR_BN254_fexp(&right);

    bool valid = FP12_BN254_equals(&left, &right);

    if (valid) {
        printf("verified successfully.\n");
    } else {
        printf("verification failed.\n");
    }

    end1 = clock();
    cpu_time_used = ((double)(end1 - start1)) / CLOCKS_PER_SEC;
    printf("cpu_time_used: %f s\n", cpu_time_used);
    return 0;
}*/
#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include "miracl_core_c_bn254/pair_BN254.h"
#include "miracl_core_c_bn254/big_256_56.h"

typedef ECP_BN254 ECP;
typedef ECP2_BN254 ECP2;
typedef FP12_BN254 FP12;
typedef BIG_256_56 BIG;

#define ell 4096
static int count = 5;

/* public parameters */
typedef struct
{
    ECP P;
    ECP2 Phat;
    BIG r;
} PP_t;

typedef struct
{
    ECP Psc[ell + 1];
    ECP2 Phatsc[ell + 1];
} ctx;

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

    for (int i = 0; i < ell + 1; i++) {
        // Psc[i] = a^i * P
        ECP_BN254_copy(&PPxa->Psc[i], &tmp1);
        ECP_BN254_mul(&tmp1, a);
        // Phatsc[i] = a^i * Phat
        ECP2_BN254_copy(&PPxa->Phatsc[i], &tmp2);
        ECP2_BN254_mul(&tmp2, a);
    }
}

void attriGen(PP_t *PP, ctx *PPxa, BIG *attri, ECP *result)
{
    // 使用堆分配代替栈数组
    BIG *F = (BIG *)malloc((ell + 1) * sizeof(BIG));
    BIG *temp = (BIG *)malloc((ell + 1) * sizeof(BIG));
    
    if (F == NULL || temp == NULL) {
        printf("Memory allocation failed in attriGen\n");
        if (F) free(F);
        if (temp) free(temp);
        return;
    }

    BIG zero, one, p;
    BIG_256_56_zero(zero);
    BIG_256_56_one(one);
    BIG_256_56_copy(p, PP->r);

    // 初始化 f(x) = 1
    BIG_256_56_copy(F[0], one);
    for (int i = 1; i <= ell; i++) {
        BIG_256_56_zero(F[i]);
        BIG_256_56_zero(temp[i]);
    }

    // 多项式乘法迭代
    for (int i = 0; i < ell; i++) {
        // temp[j] = F[j]
        for (int j = 0; j <= ell; j++) {
            BIG_256_56_copy(temp[j], F[j]);
        }

        for (int j = 0; j <= i + 1; j++) {
            BIG t1, t2;
            BIG_256_56_zero(t1);
            BIG_256_56_zero(t2);

            if (j <= i) {
                BIG_256_56_modmul(t1, temp[j], attri[i], p);
                BIG_256_56_sub(t1, p, t1);
                BIG_256_56_mod(t1, p);
            }

            if (j > 0) {
                BIG_256_56_copy(t2, temp[j - 1]);
            }
            BIG_256_56_add(F[j], t1, t2);
            BIG_256_56_mod(F[j], p);
        }
    }

    ECP_BN254_inf(result);

    for (int i = 0; i <= ell; i++) {
        ECP tempP;
        BIG scalar;
        BIG_256_56_copy(scalar, F[i]);
        ECP_BN254_copy(&tempP, &PPxa->Psc[i]);
        ECP_BN254_mul(&tempP, scalar);
        ECP_BN254_add(result, &tempP);
    }

    // 释放堆内存
    free(F);
    free(temp);
}

void GxGen(PP_t *PP, ctx *PPxa, BIG *attri, ECP *result, int count)
{
    // 使用堆分配
    BIG *G = (BIG *)malloc((count + 1) * sizeof(BIG));
    BIG *temp = (BIG *)malloc((count + 1) * sizeof(BIG));
    
    if (G == NULL || temp == NULL) {
        printf("Memory allocation failed in GxGen\n");
        if (G) free(G);
        if (temp) free(temp);
        return;
    }

    BIG zero, one, p;
    BIG_256_56_zero(zero);
    BIG_256_56_one(one);
    BIG_256_56_copy(p, PP->r);

    // 初始化 f(x) = 1
    BIG_256_56_copy(G[0], one);
    for (int i = 1; i <= count; i++) {
        BIG_256_56_zero(G[i]);
        BIG_256_56_zero(temp[i]);
    }

    // 多项式乘法迭代
    for (int i = 0; i < count; i++) {
        for (int j = 0; j <= count; j++) {
            BIG_256_56_copy(temp[j], G[j]);
        }

        for (int j = 0; j <= i + 1; j++) {
            BIG t1, t2;
            BIG_256_56_zero(t1);
            BIG_256_56_zero(t2);

            if (j <= i) {
                BIG_256_56_modmul(t1, temp[j], attri[i], p);
                BIG_256_56_modneg(t1, t1, p);
            }

            if (j > 0) {
                BIG_256_56_copy(t2, temp[j - 1]);
            }
            BIG_256_56_add(G[j], t1, t2);
            BIG_256_56_mod(G[j], p);
        }
    }

    // 初始化结果点
    ECP_BN254_inf(result);

    for (int i = 0; i <= count; i++) {
        ECP tempP;
        BIG scalar;
        BIG_256_56_copy(scalar, G[i]);
        ECP_BN254_copy(&tempP, &PPxa->Psc[i]);
        ECP_BN254_mul(&tempP, scalar);
        ECP_BN254_add(result, &tempP);
    }

    free(G);
    free(temp);
}

void HxGen(PP_t *PP, ctx *PPxa, BIG *attri, ECP2 *result, int count)
{
    // 使用堆分配
    BIG *H = (BIG *)malloc((count + 1) * sizeof(BIG));
    BIG *temp = (BIG *)malloc((count + 1) * sizeof(BIG));
    
    if (H == NULL || temp == NULL) {
        printf("Memory allocation failed in HxGen\n");
        if (H) free(H);
        if (temp) free(temp);
        return;
    }

    BIG zero, one, p;
    BIG_256_56_zero(zero);
    BIG_256_56_one(one);
    BIG_256_56_copy(p, PP->r);

    // 初始化 f(x) = 1
    BIG_256_56_copy(H[0], one);
    for (int i = 1; i <= count; i++) {
        BIG_256_56_zero(H[i]);
        BIG_256_56_zero(temp[i]);
    }

    // 多项式乘法迭代
    for (int i = 0; i < count; i++) {
        for (int j = 0; j <= count; j++) {
            BIG_256_56_copy(temp[j], H[j]);
        }

        for (int j = 0; j <= i + 1; j++) {
            BIG t1, t2;
            BIG_256_56_zero(t1);
            BIG_256_56_zero(t2);

            if (j <= i) {
                BIG_256_56_modmul(t1, temp[j], attri[i], p);
                BIG_256_56_modneg(t1, t1, p);
            }

            if (j > 0) {
                BIG_256_56_copy(t2, temp[j - 1]);
            }
            BIG_256_56_add(H[j], t1, t2);
            BIG_256_56_mod(H[j], p);
        }
    }

    // 初始化结果点
    ECP2_BN254_inf(result);

    for (int i = 0; i <= count; i++) {
        ECP2 tempP;
        BIG scalar;
        BIG_256_56_copy(scalar, H[i]);
        ECP2_BN254_copy(&tempP, &PPxa->Phatsc[i]);
        ECP2_BN254_mul(&tempP, scalar);
        ECP2_BN254_add(result, &tempP);
    }

    free(H);
    free(temp);
}

int main()
{
    clock_t start, end, start1, end1;
    double cpu_time_used, step_time_used;

    ctx PPxa;
    csprng RNG;
    PP_t PP;
    SCGen(&PP, &RNG, &PPxa);

    ECP result;
    ECP resultG;
    ECP2 resultH;
    
    // 使用堆分配主函数中的大数组
    BIG *attri = (BIG *)malloc(ell * sizeof(BIG));
    BIG *attriH = (BIG *)malloc(count * sizeof(BIG));
    BIG *attriG = (BIG *)malloc((ell - count) * sizeof(BIG));

    if (attri == NULL || attriH == NULL || attriG == NULL) {
        printf("Memory allocation failed in main\n");
        if (attri) free(attri);
        if (attriH) free(attriH);
        if (attriG) free(attriG);
        return -1;
    }

    for (int i = 0; i < ell; i++) {
        BIG m;
        BIG_256_56_randomnum(m, PP.r, &RNG);
        BIG_256_56_copy(attri[i], m);
    }

    for (int i = 0; i < ell - count; i++) {
        BIG_256_56_copy(attriG[i], attri[i]);
    }

    for (int i = 0; i < count; i++) {
        BIG_256_56_copy(attriH[i], attri[ell - count + i]);
    }

    start = clock();
    attriGen(&PP, &PPxa, attri, &result);
    end = clock();
    step_time_used = ((double)(end - start)) / CLOCKS_PER_SEC;
    printf("step_time_used: %f s\n", step_time_used);

    start1 = clock();
    GxGen(&PP, &PPxa, attriG, &resultG, ell - count);
    HxGen(&PP, &PPxa, attriH, &resultH, count);

    FP12 left, right;
    PAIR_BN254_ate(&left, &PP.Phat, &result);
    PAIR_BN254_fexp(&left);

    PAIR_BN254_ate(&right, &resultH, &resultG);
    PAIR_BN254_fexp(&right);

    bool valid = FP12_BN254_equals(&left, &right);

    if (valid) {
        printf("verified successfully.\n");
    } else {
        printf("verification failed.\n");
    }

    end1 = clock();
    cpu_time_used = ((double)(end1 - start1)) / CLOCKS_PER_SEC;
    printf("cpu_time_used: %f s\n", cpu_time_used);

    // 释放主函数中的堆内存
    free(attri);
    free(attriH);
    free(attriG);

    return 0;
}