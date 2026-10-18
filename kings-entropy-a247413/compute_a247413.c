#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <mpdecimal.h>

/* OEIS A247413: hard-core lattice gas on the king's graph (non-attacking kings),
 * entropy constant kappa = lim A063443(n)^(1/n^2) = 1.3426439511246012978517301...
 *
 * Method: row-to-row transfer-matrix renormalization (TMRG / DMRG style) in
 * 75-digit decimal arithmetic (mpdecimal). For each bond dimension m it finds the
 * dominant eigenvector Psi of the row transfer matrix by power iteration, builds a
 * reduced basis from the density matrix rho = Psi Psi^T, and reports
 * kappa = sqrt(lambda_{2N+2} / lambda_{2N}).
 *
 * main() prints the estimate for m = 16, 18, 20, 22, 24. The first 26 digits are
 * identical for every m >= 18. This is a numerical computation, not a proof.
 * A separate corner-transfer-matrix run agreed with it to about 1e-28.
 *
 * Build:  cc -O2 compute_a247413.c -lmpdec -o compute_a247413
 * Run:    ./compute_a247413        (a few minutes on one core)
 *
 * Anzal Abidi, October 2026.
 */
static mpd_context_t ctx;
#define MAX_D 64

typedef struct {
    int r, c;
    mpd_t *m[MAX_D][MAX_D];
} Mat;

static mpd_t *mpd_from_i(long v) {
    mpd_t *x = mpd_new(&ctx);
    mpd_set_i64(x, v, &ctx);
    return x;
}

static mpd_t *mpd_from_s(const char *s) {
    mpd_t *x = mpd_new(&ctx);
    mpd_set_string(x, s, &ctx);
    return x;
}

static void mat_init(Mat *A, int r, int c) {
    A->r = r; A->c = c;
    for (int i = 0; i < r; i++)
        for (int j = 0; j < c; j++)
            A->m[i][j] = mpd_from_i(0);
}

static void mat_free(Mat *A) {
    for (int i = 0; i < A->r; i++)
        for (int j = 0; j < A->c; j++)
            mpd_del(A->m[i][j]);
}

static void mat_mul(const Mat *A, const Mat *B, Mat *C) {
    mat_init(C, A->r, B->c);
    mpd_t *t = mpd_new(&ctx);
    for (int i = 0; i < A->r; i++) {
        for (int k = 0; k < A->c; k++) {
            if (mpd_iszero(A->m[i][k])) continue;
            for (int j = 0; j < B->c; j++) {
                mpd_mul(t, A->m[i][k], B->m[k][j], &ctx);
                mpd_add(C->m[i][j], C->m[i][j], t, &ctx);
            }
        }
    }
    mpd_del(t);
}

static void mat_trans(const Mat *A, Mat *AT) {
    mat_init(AT, A->c, A->r);
    for (int i = 0; i < A->r; i++)
        for (int j = 0; j < A->c; j++)
            mpd_copy(AT->m[j][i], A->m[i][j], &ctx);
}

static void sym_jacobi(const Mat *M_in, mpd_t *vals[MAX_D], Mat *V_out) {
    int n = M_in->r;
    Mat A, V;
    mat_init(&A, n, n);
    mat_init(&V, n, n);
    mpd_t *half = mpd_from_s("0.5");
    for (int i = 0; i < n; i++) {
        mpd_set_i64(V.m[i][i], 1, &ctx);
        for (int j = 0; j < n; j++) {
            mpd_add(A.m[i][j], M_in->m[i][j], M_in->m[j][i], &ctx);
            mpd_mul(A.m[i][j], A.m[i][j], half, &ctx);
        }
    }
    mpd_t *eps = mpd_from_s("1e-65");
    mpd_t *tiny = mpd_from_s("1e-68");
    mpd_t *one = mpd_from_i(1), *two = mpd_from_i(2);
    mpd_t *apq = mpd_new(&ctx), *diff = mpd_new(&ctx), *tau = mpd_new(&ctx);
    mpd_t *root = mpd_new(&ctx), *t = mpd_new(&ctx), *c = mpd_new(&ctx);
    mpd_t *s = mpd_new(&ctx), *tau_rot = mpd_new(&ctx), *h = mpd_new(&ctx);
    mpd_t *g = mpd_new(&ctx), *eh = mpd_new(&ctx), *tmp1 = mpd_new(&ctx), *tmp2 = mpd_new(&ctx);

    for (int sweep = 0; sweep < 22; sweep++) {
        int changed = 0;
        for (int p = 0; p < n; p++) {
            for (int q = p + 1; q < n; q++) {
                mpd_abs(apq, A.m[p][q], &ctx);
                if (mpd_cmp(apq, eps, &ctx) > 0) {
                    changed = 1;
                    mpd_sub(diff, A.m[q][q], A.m[p][p], &ctx);
                    mpd_abs(tmp1, diff, &ctx);
                    if (mpd_cmp(tmp1, tiny, &ctx) < 0) {
                        if (!mpd_isnegative(A.m[p][q])) mpd_copy(t, one, &ctx);
                        else mpd_minus(t, one, &ctx);
                    } else {
                        mpd_mul(tmp1, two, A.m[p][q], &ctx);
                        mpd_div(tau, diff, tmp1, &ctx);
                        mpd_mul(tmp1, tau, tau, &ctx);
                        mpd_add(tmp1, tmp1, one, &ctx);
                        mpd_sqrt(root, tmp1, &ctx);
                        if (!mpd_isnegative(tau)) {
                            mpd_add(tmp1, tau, root, &ctx);
                            mpd_div(t, one, tmp1, &ctx);
                        } else {
                            mpd_sub(tmp1, root, tau, &ctx);
                            mpd_div(t, one, tmp1, &ctx);
                            mpd_minus(t, t, &ctx);
                        }
                    }
                    mpd_mul(tmp1, t, t, &ctx);
                    mpd_add(tmp1, tmp1, one, &ctx);
                    mpd_sqrt(tmp1, tmp1, &ctx);
                    mpd_div(c, one, tmp1, &ctx);
                    mpd_mul(s, t, c, &ctx);
                    mpd_add(tmp1, one, c, &ctx);
                    mpd_div(tau_rot, s, tmp1, &ctx);
                    mpd_mul(h, t, A.m[p][q], &ctx);
                    mpd_sub(A.m[p][p], A.m[p][p], h, &ctx);
                    mpd_add(A.m[q][q], A.m[q][q], h, &ctx);
                    mpd_set_i64(A.m[p][q], 0, &ctx);
                    mpd_set_i64(A.m[q][p], 0, &ctx);
                    for (int r = 0; r < n; r++) {
                        if (r != p && r != q) {
                            mpd_copy(g, A.m[r][p], &ctx);
                            mpd_copy(eh, A.m[r][q], &ctx);
                            mpd_mul(tmp1, g, tau_rot, &ctx);
                            mpd_add(tmp1, eh, tmp1, &ctx);
                            mpd_mul(tmp1, s, tmp1, &ctx);
                            mpd_sub(A.m[r][p], g, tmp1, &ctx);
                            mpd_copy(A.m[p][r], A.m[r][p], &ctx);

                            mpd_mul(tmp1, eh, tau_rot, &ctx);
                            mpd_sub(tmp1, g, tmp1, &ctx);
                            mpd_mul(tmp1, s, tmp1, &ctx);
                            mpd_add(A.m[r][q], eh, tmp1, &ctx);
                            mpd_copy(A.m[q][r], A.m[r][q], &ctx);
                        }
                    }
                    for (int r = 0; r < n; r++) {
                        mpd_copy(g, V.m[r][p], &ctx);
                        mpd_copy(eh, V.m[r][q], &ctx);
                        mpd_mul(tmp1, g, tau_rot, &ctx);
                        mpd_add(tmp1, eh, tmp1, &ctx);
                        mpd_mul(tmp1, s, tmp1, &ctx);
                        mpd_sub(V.m[r][p], g, tmp1, &ctx);

                        mpd_mul(tmp1, eh, tau_rot, &ctx);
                        mpd_sub(tmp1, g, tmp1, &ctx);
                        mpd_mul(tmp1, s, tmp1, &ctx);
                        mpd_add(V.m[r][q], eh, tmp1, &ctx);
                    }
                }
            }
        }
        if (!changed) break;
    }
    int ord[MAX_D];
    for (int i = 0; i < n; i++) ord[i] = i;
    for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
            mpd_abs(tmp1, A.m[ord[i]][ord[i]], &ctx);
            mpd_abs(tmp2, A.m[ord[j]][ord[j]], &ctx);
            if (mpd_cmp(tmp2, tmp1, &ctx) > 0) {
                int ti = ord[i]; ord[i] = ord[j]; ord[j] = ti;
            }
        }
    }
    mat_init(V_out, n, n);
    for (int i = 0; i < n; i++) {
        vals[i] = mpd_from_i(0);
        mpd_copy(vals[i], A.m[ord[i]][ord[i]], &ctx);
        for (int r = 0; r < n; r++)
            mpd_copy(V_out->m[r][i], V.m[r][ord[i]], &ctx);
    }
    mat_free(&A); mat_free(&V);
    mpd_del(half); mpd_del(eps); mpd_del(tiny); mpd_del(one); mpd_del(two);
    mpd_del(apq); mpd_del(diff); mpd_del(tau); mpd_del(root);
    mpd_del(t); mpd_del(c); mpd_del(s); mpd_del(tau_rot);
    mpd_del(h); mpd_del(g); mpd_del(eh); mpd_del(tmp1); mpd_del(tmp2);
}

static void apply_T_row(Mat H[2][2], Mat Psi[2][2], int sz[2], mpd_t *lam_out) {
    Mat nPsi[2][2];
    for (int aL = 0; aL < 2; aL++)
        for (int aR = 0; aR < 2; aR++)
            mat_init(&nPsi[aL][aR], sz[aL], sz[aR]);

    for (int aL = 0; aL < 2; aL++) {
        for (int aR = 0; aR < 2; aR++) {
            if (aL + aR > 1) continue;
            for (int bL = 0; bL < 2; bL++) {
                if (aL + bL > 1) continue;
                for (int bR = 0; bR < 2; bR++) {
                    if (aR + bR > 1 || aL + aR + bL + bR > 1) continue;
                    Mat tmp, HR_T, prod;
                    mat_mul(&H[aL][bL], &Psi[bL][bR], &tmp);
                    mat_trans(&H[aR][bR], &HR_T);
                    mat_mul(&tmp, &HR_T, &prod);
                    for (int i = 0; i < sz[aL]; i++)
                        for (int j = 0; j < sz[aR]; j++)
                            mpd_add(nPsi[aL][aR].m[i][j], nPsi[aL][aR].m[i][j], prod.m[i][j], &ctx);
                    mat_free(&tmp); mat_free(&HR_T); mat_free(&prod);
                }
            }
        }
    }
    mpd_t *half = mpd_from_s("0.5"), *avg = mpd_new(&ctx);
    for (int i = 0; i < sz[0]; i++) {
        for (int j = i + 1; j < sz[0]; j++) {
            mpd_add(avg, nPsi[0][0].m[i][j], nPsi[0][0].m[j][i], &ctx);
            mpd_mul(avg, avg, half, &ctx);
            mpd_copy(nPsi[0][0].m[i][j], avg, &ctx);
            mpd_copy(nPsi[0][0].m[j][i], avg, &ctx);
        }
    }
    for (int i = 0; i < sz[0]; i++) {
        for (int j = 0; j < sz[1]; j++) {
            mpd_add(avg, nPsi[0][1].m[i][j], nPsi[1][0].m[j][i], &ctx);
            mpd_mul(avg, avg, half, &ctx);
            mpd_copy(nPsi[0][1].m[i][j], avg, &ctx);
            mpd_copy(nPsi[1][0].m[j][i], avg, &ctx);
        }
    }
    /* Rayleigh quotient num / den */
    mpd_t *num = mpd_from_i(0), *den = mpd_from_i(0), *norm_sq = mpd_from_i(0), *sq = mpd_new(&ctx);
    for (int aL = 0; aL < 2; aL++) {
        for (int aR = 0; aR < 2; aR++) {
            if (aL + aR > 1) continue;
            for (int i = 0; i < sz[aL]; i++) {
                for (int j = 0; j < sz[aR]; j++) {
                    mpd_mul(sq, Psi[aL][aR].m[i][j], nPsi[aL][aR].m[i][j], &ctx);
                    mpd_add(num, num, sq, &ctx);
                    mpd_mul(sq, Psi[aL][aR].m[i][j], Psi[aL][aR].m[i][j], &ctx);
                    mpd_add(den, den, sq, &ctx);
                    mpd_mul(sq, nPsi[aL][aR].m[i][j], nPsi[aL][aR].m[i][j], &ctx);
                    mpd_add(norm_sq, norm_sq, sq, &ctx);
                }
            }
        }
    }
    mpd_div(lam_out, num, den, &ctx);
    mpd_sqrt(sq, norm_sq, &ctx);
    for (int aL = 0; aL < 2; aL++) {
        for (int aR = 0; aR < 2; aR++) {
            for (int i = 0; i < sz[aL]; i++)
                for (int j = 0; j < sz[aR]; j++)
                    if (aL + aR <= 1) mpd_div(Psi[aL][aR].m[i][j], nPsi[aL][aR].m[i][j], sq, &ctx);
            mat_free(&nPsi[aL][aR]);
        }
    }
    mpd_del(half); mpd_del(avg); mpd_del(num); mpd_del(den); mpd_del(norm_sq); mpd_del(sq);
}

static void run_tmrg_indep(int m_max, int steps) {
    Mat H[2][2], Psi_s[2][2];
    for (int a = 0; a < 2; a++) {
        for (int b = 0; b < 2; b++) {
            mat_init(&H[a][b], 1, 1);
            mat_init(&Psi_s[a][b], 1, 1);
            if (a + b <= 1) {
                mpd_set_i64(H[a][b].m[0][0], 1, &ctx);
                mpd_set_i64(Psi_s[a][b].m[0][0], 1, &ctx);
            }
        }
    }
    mpd_t *lam_s = mpd_from_i(1), *lam_e = mpd_from_i(1), *kappa = mpd_from_i(1);

    for (int step = 0; step < steps; step++) {
        int sz_old[2] = {H[0][0].r, H[1][0].r};
        int n_it_s = (step == steps - 1) ? 45 : 6;
        for (int it = 0; it < n_it_s; it++)
            apply_T_row(H, Psi_s, sz_old, lam_s);

        int sz_exp[2] = {sz_old[0] + sz_old[1], sz_old[0]};
        Mat H_exp[2][2], Psi_e[2][2];
        for (int a = 0; a < 2; a++) {
            for (int b = 0; b < 2; b++) {
                mat_init(&H_exp[a][b], sz_exp[a], sz_exp[b]);
                mat_init(&Psi_e[a][b], sz_exp[a], sz_exp[b]);
                if (a + b <= 1) {
                    int r_off = 0;
                    for (int c = 0; c < 2; c++) {
                        if (a + c > 1) continue;
                        int mc = sz_old[c];
                        int c_off = 0;
                        for (int d = 0; d < 2; d++) {
                            if (b + d > 1) continue;
                            int md = sz_old[d];
                            if (a + b + c + d <= 1) {
                                for (int i = 0; i < mc; i++) {
                                    for (int j = 0; j < md; j++) {
                                        mpd_copy(H_exp[a][b].m[r_off + i][c_off + j], H[c][d].m[i][j], &ctx);
                                        mpd_copy(Psi_e[a][b].m[r_off + i][c_off + j], Psi_s[c][d].m[i][j], &ctx);
                                    }
                                }
                            }
                            c_off += md;
                        }
                        r_off += mc;
                    }
                }
            }
        }
        int n_it_e = (step == steps - 1) ? 55 : 8;
        for (int it = 0; it < n_it_e; it++)
            apply_T_row(H_exp, Psi_e, sz_exp, lam_e);

        mpd_div(kappa, lam_e, lam_s, &ctx);
        mpd_sqrt(kappa, kappa, &ctx);

        if (step == steps - 1) {
            char *s = mpd_to_sci(kappa, 1);
            printf("Independent TMRG (rho_L basis) m_max=%2d: %.42s\n", m_max, s);
            mpd_free(s);
            for (int a = 0; a < 2; a++)
                for (int b = 0; b < 2; b++) {
                    mat_free(&H_exp[a][b]); mat_free(&Psi_e[a][b]);
                }
            break;
        }

        Mat U[2];
        for (int aL = 0; aL < 2; aL++) {
            int sL = sz_exp[aL];
            Mat rho;
            mat_init(&rho, sL, sL);
            for (int aR = 0; aR < 2; aR++) {
                if (aL + aR > 1) continue;
                Mat PT, prod;
                mat_trans(&Psi_e[aL][aR], &PT);
                mat_mul(&Psi_e[aL][aR], &PT, &prod);
                for (int i = 0; i < sL; i++)
                    for (int j = 0; j < sL; j++)
                        mpd_add(rho.m[i][j], rho.m[i][j], prod.m[i][j], &ctx);
                mat_free(&PT); mat_free(&prod);
            }
            mpd_t *vals[MAX_D];
            Mat vecs;
            sym_jacobi(&rho, vals, &vecs);
            int keep = (sL < m_max) ? sL : m_max;
            mat_init(&U[aL], sL, keep);
            for (int i = 0; i < sL; i++)
                for (int j = 0; j < keep; j++)
                    mpd_copy(U[aL].m[i][j], vecs.m[i][j], &ctx);
            for (int i = 0; i < sL; i++) mpd_del(vals[i]);
            mat_free(&rho); mat_free(&vecs);
        }

        for (int a = 0; a < 2; a++) {
            Mat UaT;
            mat_trans(&U[a], &UaT);
            for (int b = 0; b < 2; b++) {
                mat_free(&H[a][b]);
                mat_free(&Psi_s[a][b]);
                if (a + b > 1) {
                    mat_init(&H[a][b], U[a].c, U[b].c);
                    mat_init(&Psi_s[a][b], U[a].c, U[b].c);
                } else {
                    Mat t1, p1, t2, p2;
                    mat_mul(&UaT, &H_exp[a][b], &t1);
                    mat_mul(&t1, &U[b], &p1);
                    mat_init(&H[a][b], U[a].c, U[b].c);
                    for (int i = 0; i < U[a].c; i++)
                        for (int j = 0; j < U[b].c; j++)
                            mpd_div(H[a][b].m[i][j], p1.m[i][j], kappa, &ctx);

                    mat_mul(&UaT, &Psi_e[a][b], &t2);
                    mat_mul(&t2, &U[b], &p2);
                    mat_init(&Psi_s[a][b], U[a].c, U[b].c);
                    for (int i = 0; i < U[a].c; i++)
                        for (int j = 0; j < U[b].c; j++)
                            mpd_copy(Psi_s[a][b].m[i][j], p2.m[i][j], &ctx);
                    mat_free(&t1); mat_free(&p1); mat_free(&t2); mat_free(&p2);
                }
                mat_free(&H_exp[a][b]);
                mat_free(&Psi_e[a][b]);
            }
            mat_free(&UaT);
        }
        mat_free(&U[0]); mat_free(&U[1]);
    }
    for (int a = 0; a < 2; a++)
        for (int b = 0; b < 2; b++) {
            mat_free(&H[a][b]); mat_free(&Psi_s[a][b]);
        }
    mpd_del(lam_s); mpd_del(lam_e); mpd_del(kappa);
}

int main(void) {
    mpd_init(&ctx, 75);
    int ms[5] = {16, 18, 20, 22, 24};
    for (int i = 0; i < 5; i++) {
        run_tmrg_indep(ms[i], 48);
        fflush(stdout);
    }
    return 0;
}
