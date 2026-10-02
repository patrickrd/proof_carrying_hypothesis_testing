# cantelli_bounds.R
# 24 Sep 2026: nonuniform Berry-Esseen constant changed from Paditz 1989 (31.935) to Shevtsova 2017 (21.82,
#   general non-i.i.d. case; Inequalities and Extremal Problems in Probability and Statistics, ed. Pinelis, pp. 47-102),
#   the best established value per Shevtsova arXiv:2001.01123 Table 1. Uniform constant 0.5583: Shevtsova 2013/2014. -- <2026-09-19> new misspecification-free normal-approximation bound
# (the Cantelli derivation in the paper's appendix):
#   P(|T_norm| >= t) <= 2{1-Phi(t s\theta)} + 2 rhobar min{0.5583, 21.82/(1+t s\theta)^3}
#                        + term3(theta),   s\theta = sqrt(theta)
#   term3 = q/(1+q):  analytic  q = qbar = V0/a-^2 + smax^2 gmax/a- + (3 sqrt3/4) b3 smax^3 S sqrt(gmax)/a-^{3/2}
#                     numeric   q = sup_{x=rho^2>=0} (V0 + 4 smax^2 gmax x + 4 b3 smax^3 S sqrt(gmax) sqrt(x))/(x+a-)^2
#   a-(theta) = smin^2 sum_{c_j>=0} c_j + smax^2 sum_{c_j<0} c_j,  c_j = Q_jj - theta gam_j^2,
#   Q = (I-H) diag(gam^2 d) (I-H), V0 = smax^4 {(k-1) sum Q_ii^2 + 2 sum_{i!=j} Q_ij^2},
#   gmax = max gam_i^2 d_i, S = sqrt(sum Q_ii^2). Applicability: a-(theta) > 0 (auto for HC3).
# Best-chance instantiation as before: smin = smax = 1 (equal variances), kappa = 3,
# b3 = sqrt(8/pi) (Gaussian moments). No misspecification tolerance (that is the point).
# HC0 and HC3 both computed; t0 is the matching HC-studentised statistic.
suppressMessages(source("conservative_bounds.R"))  # designs, hc0_t, strep/anorexia/SH0ES objects
shoes <- list(X = Xs, y = ys, a = a)               # capture SH0ES design before names reused

cantelli_p <- function(X, y, a, v0 = 0, variant = "HC0", kappa = 3, b3 = sqrt(8/pi),
                       sratio = 1, n_theta = 2000) {
  X <- as.matrix(X); n <- nrow(X)
  XtXi <- solve(crossprod(X))
  gam <- as.vector(X %*% XtXi %*% a)
  H <- X %*% XtXi %*% t(X)
  h <- diag(H)
  d <- if (variant == "HC3") 1/(1 - h)^2 else rep(1, n)
  bh <- XtXi %*% crossprod(X, y)
  e <- as.vector(y - X %*% bh)
  u <- abs(sum(a * bh) - v0)
  D2 <- sum(gam^2 * d * e^2)
  t0 <- u / sqrt(D2)
  smin <- 1; smax <- sratio
  W <- gam^2 * d
  IH <- diag(n) - H
  Q <- IH %*% (W * IH)                      # (I-H) diag(W) (I-H)
  Qd <- diag(Q); SQ2 <- sum(Qd^2); offd2 <- sum(Q^2) - SQ2
  gmax <- max(W); S <- sqrt(SQ2)
  V0 <- smax^4 * ((kappa - 1) * SQ2 + 2 * offd2)
  cS <- 4 * b3 * smax^3 * S * sqrt(gmax)    # coefficient of sqrt(x)
  cL <- 4 * smax^2 * gmax                   # coefficient of x
  rhobar <- b3 * sratio^3 * sum(abs(gam)^3) / sum(gam^2)^1.5

  thetas <- seq(1e-4, 1 - 1e-4, length.out = n_theta)
  gam2 <- gam^2
  term12 <- function(th) { z <- t0 * sqrt(th)
    2 * (1 - pnorm(z)) + 2 * rhobar * pmin(0.5583, 21.82 / (1 + z)^3) }
  supq_num <- function(am) {                # sup over x >= 0 of (V0 + cL x + cS sqrt(x))/(x+am)^2
    f <- function(lx) { x <- exp(lx); (V0 + cL * x + cS * sqrt(x)) / (x + am)^2 }
    lxs <- log(am) + seq(-20, 20, length.out = 200)
    q0 <- V0 / am^2                          # x = 0 endpoint
    j <- which.max(vapply(lxs, f, 0))
    lo <- lxs[max(1, j - 1)]; hi <- lxs[min(length(lxs), j + 1)]
    max(q0, optimize(f, c(lo, hi), maximum = TRUE, tol = 1e-12)$objective)
  }
  best <- c(analytic = Inf, numeric = Inf); th_at <- c(analytic = NA, numeric = NA)
  for (th in thetas) {
    cj <- Qd - th * gam2
    am <- smin^2 * sum(cj[cj >= 0]) + smax^2 * sum(cj[cj < 0])
    if (am <= 0) next
    t12 <- term12(th)
    if (t12 > min(best)) next                # cannot improve either
    qbar <- V0 / am^2 + smax^2 * gmax / am + (3 * sqrt(3) / 4) * b3 * smax^3 * S * sqrt(gmax) / am^1.5
    pa <- t12 + qbar / (1 + qbar)
    if (pa < best["analytic"]) { best["analytic"] <- pa; th_at["analytic"] <- th }
    qn <- supq_num(am)
    pn <- t12 + qn / (1 + qn)
    if (pn < best["numeric"]) { best["numeric"] <- pn; th_at["numeric"] <- th }
  }
  list(t0 = t0, hmax = max(h),
       analytic = min(1, best["analytic"]), numeric = min(1, best["numeric"]),
       theta = th_at)
}

## assemble the 17-row exhibit (mirrors results_v3b.csv rows)
rows <- list()
for (nm in names(smax)) { D <- designs[[nm]]
  rows[[nm]] <- list(X = D$X, y = D$y, a = D$a, v0 = 0) }
dd <- strep_tb; died <- as.numeric(dd$radiologic_6m == "1_Death")
trt <- as.numeric(dd$arm == "Streptomycin")
rows[["strep"]] <- list(X = cbind(1, trt), y = died, a = c(0, 1), v0 = 0)
an <- anorexia[anorexia$Treat %in% c("FT", "Cont"), ]
rows[["anorexia"]] <- list(X = cbind(1, as.numeric(an$Treat == "FT")),
                           y = an$Postwt - an$Prewt, a = c(0, 1), v0 = 0)
rows[["SH0ES"]] <- list(X = shoes$X, y = shoes$y, a = shoes$a, v0 = 5 * log10(67.36))
v0c <- (1/(6000 * (60^2 * 24 * 365))) * 3.09e19
hb <- designs[["hubble_teach"]]; h29 <- designs[["Hubble1929"]]
rows[["hubble_creationist"]]   <- list(X = matrix(hb$X[, 2], ncol = 1), y = hb$y, a = 1, v0 = v0c)
rows[["Hubble1929_creationist"]] <- list(X = matrix(h29$X[, 2], ncol = 1), y = h29$y, a = 1, v0 = v0c)
## RR redesign (HAP Table 4 four-category design)
rr <- read.csv("dataset_story_data/RR-processed.csv")
rr <- rr[!is.na(rr$dRGDP) & !is.na(rr$debtgdp), ]
Xr <- cbind(1, as.numeric(rr$debtgdp >= 30 & rr$debtgdp < 60),
            as.numeric(rr$debtgdp >= 60 & rr$debtgdp < 90), as.numeric(rr$debtgdp >= 90))
rows[["ReinhartRogoff"]] <- list(X = Xr, y = rr$dRGDP, a = c(0, 0, 0, 1), v0 = 0)

old <- read.csv("results_v3b.csv")
out <- data.frame()
for (nm in names(rows)) { r <- rows[[nm]]
  z0 <- cantelli_p(r$X, r$y, r$a, r$v0, "HC0")
  z3 <- cantelli_p(r$X, r$y, r$a, r$v0, "HC3")
  out <- rbind(out, data.frame(dataset = nm, hmax = z0$hmax,
    old_normapx = old$normapx[match(nm, old$dataset)],
    hc0_analytic = z0$analytic, hc0_numeric = z0$numeric, t_hc0 = z0$t0,
    hc3_analytic = z3$analytic, hc3_numeric = z3$numeric, t_hc3 = z3$t0))
  cat(nm, "done\n") }
print(out, digits = 3)
write.csv(out, "cantelli_results.csv", row.names = FALSE)
cat("written cantelli_results.csv\n")
