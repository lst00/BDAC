#include <assert.h>
#include <time.h>
#include "miracl_core_c_bn254/pair_BN254.h"
#include "miracl_core_c_bn254/big_256_56.h"

typedef ECP_BN254 ECP;
typedef ECP2_BN254 ECP2;
typedef FP12_BN254 FP12;
typedef BIG_256_56 BIG;
#define MAX_USERS 10
#define ell 5
static int count = 25;
/* signature type */
//这一版是用户数量ell=5，链长count

/* public parameters */
typedef struct
{
    ECP P;
    ECP2 Phat;
    BIG r;
} PP_t;

typedef struct
{
    ECP Psc[ell * 2 ];
    ECP2 Phatsc[ell];
} ctx;

typedef struct {
    ECP2 pk[ell];
    BIG sk[ell];
    ECP2 msg_ecp2[ell];
    ECP mgs_ecp[ell][ell + 1];
} usergen;

typedef struct {
    ECP2 r_ecp2[ell];
    ECP r_ecp[ell][ell + 1];
} matrix_R;

typedef struct
{
    ECP Z;
    ECP Y;
    ECP2 Yhat;

} sigma_t;

typedef struct link {
    ECP commit[ell];
    ECP2 pk[ell];
    sigma_t sigma;
    ECP prove;
    ECP msg;
    struct link *next; 
} link_t;


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

usergen KeyGen(PP_t *PP, csprng *rng , ctx *PPxa , int start_n ) //这里的pk和之前的设置略微不同
{
    usergen user;

    for (int i = 0; i < ell ; i++)
    {
        BIG x;
        ECP2 w;
        // x ← Zp, b ← Zp
        BIG_256_56_randomnum(x, PP->r, rng);
        BIG_256_56_copy(user.sk[i], x);

        // w = x * phat
        ECP2_BN254_copy(&w, &PP->Phat);
        ECP2_BN254_mul(&w, x);
        // 存储 sk[i] = x, pk[i] = w, B[i] = b
        ECP2_BN254_copy(&user.pk[i], &w);
    }

    for(int i = 0; i < ell ; i++){

        ECP2_BN254_copy(&user.msg_ecp2[i], &user.pk[i]);
    
        int n = start_n;
        for (int j = 0; j < ell + 1; j++) {
                if (n == ell) {
                    ECP_BN254_inf(&user.mgs_ecp[i][j]);
                }  // 将 n = 5
                else{
                    ECP_BN254_copy(&user.mgs_ecp[i][j], &PPxa->Psc[n]);// 复制原始点
                    ECP_BN254_mul(&user.mgs_ecp[i][j], user.sk[i]);  // 乘 sk[i]
                }
                n++;
            }
    }

    return user;
}

void generate_users(PP_t *PP, csprng *rng , ctx *PPxa, usergen *users)
{
    int start_n = 0;
    for (int i = 0; i < ell; i++) {
        users[i] = KeyGen(PP, rng, PPxa, start_n);
        start_n ++;  // 每次调用时 n++
    }

}

matrix_R RGEN(usergen *users,int k){

    matrix_R R;
    for(int i = 0; i < ell ; i++){

        ECP2_BN254_copy(&R.r_ecp2[i], &users[i].msg_ecp2[k]);

        for (int j = 0; j < ell + 1; j++) {
                ECP_BN254_copy(&R.r_ecp[i][j], &users[i].mgs_ecp[k][j]);
            }
    }

    return R;
}

void Sign(PP_t *PP, BIG *sk, ECP *commit_j, sigma_t *sigma, csprng *rng)
{
    BIG y, y_inv;
    ECP factor;
    BIG_256_56_randomnum(y, PP->r, rng);
    BIG_256_56_invmodp(y_inv, y, PP->r);

    ECP_BN254_inf(&(sigma->Z));

    for(int i = 0; i < ell; i++){
        ECP_BN254_copy(&factor, &commit_j[i]);
        ECP_BN254_mul(&factor, sk[i]);
        ECP_BN254_add(&(sigma->Z), &factor);
    }
    ECP_BN254_mul(&(sigma->Z), y);

    ECP_BN254_copy(&(sigma->Y), &PP->P);
    ECP2_BN254_copy(&(sigma->Yhat), &PP->Phat);
    ECP_BN254_mul(&(sigma->Y), y_inv);
    ECP2_BN254_mul(&(sigma->Yhat), y_inv);


};

bool VerifyCom(PP_t *PP, ctx *PPxa, ECP *commit_j, ECP *prove_i, ECP *msg, int id)
{
    ECP commit_all,prove_all;
    ECP p;
    int idx;
    idx = ell + 1 - id;
    ECP_BN254_inf(&commit_all);
    for (int i = 0 ; i < ell ; i++){
        ECP_BN254_add(&commit_all,&commit_j[i]);
    }


    FP12 left,right,e1,e2;

    PAIR_BN254_ate(&left, &PPxa->Phatsc[idx-1], &commit_all);
    PAIR_BN254_fexp(&left);

    PAIR_BN254_double_ate(&right, &PP->Phat, prove_i, &PPxa->Phatsc[idx-1], msg);
    PAIR_BN254_fexp(&right);

    return FP12_BN254_equals(&right, &left);

}; 

bool VerifySig(PP_t *PP, ECP2 *pk, ECP *commit_j, sigma_t *sigma)
{
    FP12 result, q2, q3, q4, factor;
    PAIR_BN254_ate(&result, &pk[0], &commit_j[0]);
    PAIR_BN254_fexp(&result);
    for (int i = 1; i< ell; i++){
        PAIR_BN254_ate(&factor, &pk[i], &commit_j[i]);
        PAIR_BN254_fexp(&factor);
        FP12_BN254_mul(&result,&factor);
    }
    
    PAIR_BN254_ate(&q2, &(sigma->Yhat), &(sigma->Z));
    PAIR_BN254_fexp(&q2);

    PAIR_BN254_ate(&q3, &PP->Phat, &(sigma->Y));
    PAIR_BN254_fexp(&q3);
    PAIR_BN254_ate(&q4, &(sigma->Yhat), &PP->P);
    PAIR_BN254_fexp(&q4);

    return (bool)FP12_BN254_equals(&result, &q2) & (bool)FP12_BN254_equals(&q3, &q4);
}

void CredGen(PP_t *PP, ctx *PPxa, csprng *RNG, link_t *node, usergen *users, ECP2 *pk, BIG *sk, int id)
{

    matrix_R R[ell];
    for (int k = 0; k < ell; k++) {
        R[k] = RGEN(users, k);//这里的k就是维度j
    }
    BIG r[ell];
    for (int i = 0; i < ell ; i++)
    {
        BIG r_j;
        BIG_256_56_randomnum(r_j, PP->r, RNG);
        BIG_256_56_copy(r[i], r_j);
    }//为维度生成l个随机数rj

    ECP commit_j[ell];
    for(int i = 0 ;i < ell ;i++){
        ECP_BN254_copy(&commit_j[i],&PP->P);
        ECP_BN254_mul(&commit_j[i],r[i]);
        for (int j = 0 ; j < ell ; j++){
            ECP_BN254_add(&commit_j[i],&R[i].r_ecp[j][0]);
        }
    }

    ECP prove_j[ell];
    int idx;
    idx = ell + 1 - id; 
    for(int i = 0 ;i < ell ;i++){
        ECP_BN254_copy(&prove_j[i],&PPxa->Psc[idx - 1]);//这里的idx-1是对应数组中的位置
        ECP_BN254_mul(&prove_j[i],r[i]); 
        for (int j = 0 ; j < ell ; j++){
            ECP_BN254_add(&prove_j[i],&R[i].r_ecp[j][idx]);
        } 
    }

    ECP prove_i;
    ECP_BN254_inf(&prove_i);
    for(int i = 0;i< ell ;i++){
        ECP_BN254_add(&prove_i,&prove_j[i]);
    }

    sigma_t sigma;
    Sign(PP,sk,commit_j,&sigma,RNG);

    ECP msg;
    ECP_BN254_inf(&msg);
    for (int j = 0 ; j < ell ; j++){
        ECP_BN254_add(&msg,&users[id - 1].mgs_ecp[j][0]);
    }
    ECP_BN254_copy(&(node->msg),&msg);
    for(int i =0; i < ell; i++){
        ECP2_BN254_copy(&(node->pk[i]), &pk[i]);
        ECP_BN254_copy(&(node->commit[i]),&commit_j[i]);
    }
    ECP_BN254_copy(&(node->prove),&prove_i);
    node->sigma = sigma;
    node->next = NULL;
}

void VerifyChain(PP_t *PP, ctx *PPxa, link_t *Cred_chain, usergen *user, int id)
{
    link_t *current = Cred_chain;
    int i = 0;

    while (current != NULL) {

        bool valid = VerifySig(PP, current->pk, current->commit, &current->sigma);
        // Verify
        bool valid2 = VerifyCom(PP, PPxa, current->commit, &current->prove, &current->msg, id);
/*        if (valid && valid2) {
            printf("Verification successfully! %d\n", i);
        }else{
            printf("Verification failed at node %d \n", i);
            exit(EXIT_FAILURE); 
        }*/
        current = current->next;
        i ++ ;
    }

 //   printf("All links verified successfully.\n");
};

void FreeChain(link_t *head) {
    link_t *temp;
    while (head != NULL) {
        temp = head;
        head = head->next;
        free(temp);  // 释放当前节点
    }
}

int main()
{

    ctx PPxa;
    csprng RNG;
    PP_t PP;
    SCGen(&PP,&RNG,&PPxa);
    clock_t start0, start1, end0, end1;
    double step0, step1;
    double cpu_time_used = 0;
    double verified_time_used = 0;
    ECP2 rt_pk[ell];
    BIG rt_sk[ell];
    int id = 1;

    for (int i = 0; i < ell ; i++)
    {
        BIG x;
        ECP2 w;
        // x ← Zp, b ← Zp
        BIG_256_56_randomnum(x, PP.r, &RNG);
        BIG_256_56_copy(rt_sk[i], x);

        // w = x * phat
        ECP2_BN254_copy(&w, &PP.Phat);
        ECP2_BN254_mul(&w, x);
        // 存储 sk[i] = x, pk[i] = w, B[i] = b
        ECP2_BN254_copy(&rt_pk[i], &w);
    }

    usergen users[ell];
    generate_users(&PP,&RNG,&PPxa,users);
    link_t *Credchain = (link_t *)malloc(sizeof(link_t));
    if (Credchain == NULL) {
        // 错误处理
        printf("内存分配失败\n");
        exit(1);  // 或者其他错误处理
    }
    CredGen(&PP, &PPxa, &RNG, Credchain, users, rt_pk, rt_sk, id);
    VerifyChain(&PP, &PPxa, Credchain, &users[id - 1], id);

    link_t *current = Credchain;  // 从第一个节点开始
    link_t *new_node = NULL;  // 新生成的链表节点指针

    for (int i = 0; i < count ; i++) {
        usergen users_new[ell];
        generate_users(&PP,&RNG,&PPxa,users_new);
        new_node = (link_t *)malloc(sizeof(link_t));
        if (new_node == NULL) {
            // 错误处理
            printf("内存分配失败\n");
            exit(1);  // 或者其他错误处理
        } 
        start0 = clock();
        CredGen(&PP, &PPxa, &RNG, new_node, users_new, users[id - 1].pk, users[id - 1].sk, id);//这里强制设置每个群都是第i个人接发
        end0 = clock();
        step0 = ((double)(end0 - start0)) / CLOCKS_PER_SEC;

        start1 = clock();
        VerifyChain(&PP, &PPxa, Credchain, &users[id - 1], id);
        end1 = clock();
        step1 = ((double)(end1 - start1)) / CLOCKS_PER_SEC;

        cpu_time_used = cpu_time_used + step0;
        verified_time_used = verified_time_used + step1;

        current->next = new_node;
        current = new_node;  // 更新当前节点为新节点
        for (int i = 0; i < ell; i++) {
            users[i] = users_new[i];
        }
    }
    // 最后一个节点的 next 应该指向 NULL
    current->next = NULL;
    FreeChain(Credchain); 
    
    printf("cpu_time_used : %f s\n",cpu_time_used);
    printf("verified_time_used : %f s\n",verified_time_used);
   
    return 0;
}