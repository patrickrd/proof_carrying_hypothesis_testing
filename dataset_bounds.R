# dataset_bounds.R -- certified p-value bounds via the BE + variance-estimation route
# (the formulas machine-checked in linear-model-lean-quantitative, Ols/FiniteN.lean),
# evaluated on real datasets under favourable assumption settings:
#   r = s_max/s_min = 1 (homoscedastic), Gaussian moment ratios (kappa = 3,
#   E|e|^3 = sqrt(8/pi) sigma^3), no misspecification allowance (C_r = 0, so u = 0, rho_d = 0).
# One-sided bound (Theorem finiteN_tail_oneSided), at working threshold t <= t0, theta in (0, 1-2*hmax):
#   P(T > t) <= (1 - Phi(t)) + eta(t*sqrt(theta)) + t*(1-sqrt(theta))*phi(t*sqrt(theta)) + e_var(theta)
#   e_var(theta) = (V_plus/nu^2) / (1 - 2*hmax - theta)^2       [scale-free at r = 1]
#   V_plus/nu^2 = ((kappa-1)*sum(diag(M)^2) + 2*sum_offdiag(M^2)) / (sum gam^2)^2,
#   M = (I-H) diag(d*gam^2) (I-H),  gam_i = a' (X'X)^{-1} x_i.
# Two-sided doubles the Gaussian, eta and shift terms (eta symmetric here).
# eta from Berry-Esseen for the plain weighted sum Z = sum gam_i eps_i / sqrt(nu):
#   uniform:    |F - Phi| <= Cu * rho_n,          Cu = 0.5583 (Shevtsova 2013, non-iid)
#   nonuniform: |F - Phi| <= Cnu * rho_n/(1+|z|)^3, Cnu = 31.935 (Paditz, non-iid)
#   in-repo certified today: Cu = 30 (BerryEsseen.lean placeholder).
#   rho_n = sqrt(8/pi) * sum|gam|^3 / (sum gam^2)^{3/2}   [Gaussian third-moment ratio, r = 1]

certified <- function(X, a, t0, d = NULL, kappa = 3, b3ratio = sqrt(8/pi),
                      cr = 0, sided = 2, n_theta = 4000) {
  # cr: misspecification allowance, |r_i| <= cr * sigma. Enters V_plus only (X'r = 0 keeps
  # the contrast numerator exact): ||u||^2 <= cr^2 sum d_i^2 gam_i^4 and
  # sum M_ii |u_i| <= sqrt(sum M_ii^2) ||u|| (Lean lemmas normSq_hcU_le, sum_hcM_abs_hcU_le);
  # the helpful rho^2 term in the variance-event denominator is dropped (conservative).
  n <- nrow(X); if (is.null(d)) d <- rep(1, n)          # HC0
  XtXinv <- solve(crossprod(X))
  gam <- as.vector(X %*% XtXinv %*% a)
  H <- X %*% XtXinv %*% t(X)
  hmax <- max(diag(H))
  nu <- sum(gam^2)
  rho_n <- b3ratio * sum(abs(gam)^3) / nu^1.5
  M <- (diag(n) - H) %*% (d * gam^2 * (diag(n) - H))    # (I-H) diag(d gam^2) (I-H)
  S4 <- sum(d^2 * gam^4); SdM2 <- sum(diag(M)^2)
  Vp_nu2 <- ((kappa - 1) * SdM2 + 2 * (sum(M^2) - SdM2)
             + 4 * cr^2 * S4 + 4 * b3ratio * cr * sqrt(SdM2 * S4)) / nu^2

  etas <- list(
    none     = function(z) 0,                            # normality of Z granted
    repo30   = function(z) 30 * rho_n,                   # certified in-repo today
    best_u   = function(z) 0.5583 * rho_n,               # best published uniform
    best_unu = function(z) rho_n * pmin(0.5583, 31.935 / (1 + abs(z))^3) # headline
  )
  side <- if (sided == 2) 2 else 1
  if (1 - 2 * hmax <= 1e-4) {   # theorem hypothesis theta < 1 - 2*hmax unsatisfiable
    na <- c(bound = NA, gaussian = NA, be = NA, shift = NA, evar = NA, theta = NA)
    return(list(n = n, p = ncol(X), hmax = hmax, rho_n = rho_n, Vp_nu2 = Vp_nu2,
                t0 = t0, sided = sided, inapplicable = TRUE,
                bounds = list(none = na, repo30 = na, best_u = na, best_unu = na)))
  }
  thetas <- seq(1e-4, 1 - 2 * hmax - 1e-4, length.out = n_theta)
  out <- lapply(etas, function(eta) {
    gaussian <- side * (1 - pnorm(t0))
    be    <- side * eta(t0 * sqrt(thetas))
    shift <- side * t0 * (1 - sqrt(thetas)) * dnorm(t0 * sqrt(thetas))
    evar  <- Vp_nu2 / (1 - 2 * hmax - thetas)^2
    tot <- gaussian + be + shift + evar
    j <- which.min(tot)
    c(bound = min(1, tot[j]), gaussian = gaussian, be = be[j], shift = shift[j],
      evar = evar[j], theta = thetas[j])
  })
  list(n = n, p = ncol(X), hmax = hmax, rho_n = rho_n, Vp_nu2 = Vp_nu2,
       t0 = t0, sided = sided, bounds = out)
}

# HC0-studentised t statistic for contrast a (matches hcStudent in Lean, d = 1)
hc0_t <- function(X, y, a) {
  XtXinv <- solve(crossprod(X))
  bhat <- XtXinv %*% crossprod(X, y)
  e <- as.vector(y - X %*% bhat)
  gam <- as.vector(X %*% XtXinv %*% a)
  as.numeric(sum(a * bhat) / sqrt(sum(gam^2 * e^2)))
}

report <- function(name, X, y, a, note = "") {
  cls <- summary(lm(y ~ X - 1))
  # classical t and p for the contrast (assumes a picks one coefficient)
  j <- which(a != 0)
  ct <- cls$coefficients[j, 3]; cp <- cls$coefficients[j, 4]
  t0 <- abs(hc0_t(X, y, a))
  z <- certified(X, a, t0)
  zm <- certified(X, a, t0, cr = 0.5)   # misspecification allowance |r_i| <= 0.5 sigma
  b <- sapply(z$bounds, function(v) v["bound"])
  bm <- zm$bounds$best_unu["bound"]
  cat(sprintf("%-22s n=%4d  t_cls=%7.2f  p_cls=%9.2e  t_HC0=%7.2f  rho_n=%6.3f  hmax=%5.3f\n",
              name, z$n, ct, cp, t0, z$rho_n, z$hmax))
  cat(sprintf("   certified 2-sided: eta=0: %6.3g | C=30: %6.3g | unif .5583: %6.3g | +nonuni (wellspec): %6.3g | +nonuni (cr=0.5): %6.3g\n",
              b[1], b[2], b[3], b[4], bm))
  dec <- z$bounds$best_unu
  cat(sprintf("   headline decomposition: gaussian %.2e, BE %.3g, shift %.3g, e_var %.3g (theta=%.2f)%s\n",
              dec["gaussian"], dec["be"], dec["shift"], dec["evar"], dec["theta"],
              if (nchar(note)) paste0("  [", note, "]") else ""))
  invisible(z)
}
