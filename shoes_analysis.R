# SH0ES (Riess et al. 2022, arXiv:2112.04510) -- reproduce the published GLS fit from the
# public data release (github.com/PantheonPlusSH0ES/DataRelease, SH0ES_Data), then refit as
# diagonal-weighted least squares (independent errors with the quoted variances) and assess
# the certified bound for the H0 contrast against Planck.
# The three FITS matrices (y 3492, L 3492x47, C 3492x3492; allc via git-lfs, 48 MB) are kept
# outside the synced folder; set `scr` to their location.
# Download (allc via git-lfs media URL):
#   BASE=https://raw.githubusercontent.com/PantheonPlusSH0ES/DataRelease/main/SH0ES_Data
#   curl -sL $BASE/ally_shoes_ceph_topantheonwt6.0_112221.fits -o ally.fits    (similarly alll)
#   curl -sL https://media.githubusercontent.com/media/PantheonPlusSH0ES/DataRelease/main/SH0ES_Data/allc_shoes_ceph_topantheonwt6.0_112221.fits -o allc.fits
scr <- path.expand("~/temp/shoes_data/")
source("~/Documents/svn/wps/lean_blog/dataset_bounds.R")

read_fits <- function(f) {
  con <- file(f, "rb"); hdr <- character(0)
  repeat {
    block <- readChar(con, 2880, useBytes = TRUE)
    cards <- substring(block, seq(1, 2801, 80), seq(80, 2880, 80))
    hdr <- c(hdr, cards)
    if (any(grepl("^END *$", cards))) break
  }
  gv <- function(k) {
    x <- hdr[grepl(paste0("^", k, " *="), hdr)][1]
    if (is.na(x)) return(NA_real_)
    as.numeric(trimws(strsplit(strsplit(x, "=")[[1]][2], "/")[[1]][1]))
  }
  n1 <- gv("NAXIS1")
  n2 <- if (gv("NAXIS") >= 2) gv("NAXIS2") else 1
  stopifnot(gv("BITPIX") == -32)
  dat <- readBin(con, "numeric", n = n1 * n2, size = 4, endian = "big")
  close(con)
  matrix(dat, nrow = n2, ncol = n1, byrow = TRUE)  # NAXIS1 varies fastest
}

y  <- as.vector(read_fits(paste0(scr, "ally.fits")))
L  <- read_fits(paste0(scr, "alll.fits")); if (nrow(L) != length(y)) L <- t(L)
Cv <- read_fits(paste0(scr, "allc.fits"))

## 1. reproduce the full-covariance GLS of the release (R22 eq. 6, y = Lq + noise)
Ci_L <- solve(Cv, L); A <- crossprod(L, Ci_L)
q  <- as.vector(solve(A, crossprod(Ci_L, y)))
se <- sqrt(diag(solve(A)))
k  <- length(q)
cat("GLS H0 =", 10^(q[k]/5), "+-", 10^(q[k]/5) * log(10)/5 * se[k],
    "  (published: 73.04 +- 1.04, 5 sigma vs Planck)\n")

## 2. diagonal-weighted refit; drop column 45 (parameter fixed by a zero-variance
## pseudo-observation, estimate 0, se 0 in lstsq_results.txt)
keepc <- setdiff(1:47, 45)
w  <- 1 / sqrt(diag(Cv))
Xs <- (L * w)[, keepc]; ys <- y * w
XtXi <- solve(crossprod(Xs)); k <- ncol(Xs)
qd <- qr.solve(Xs, ys)
cat("WLS-diag H0 =", 10^(qd[k]/5), "+-", 10^(qd[k]/5) * log(10)/5 * sqrt(XtXi[k, k]), "\n")

## 3. certified assessment for the contrast 5 log10 H0 vs Planck (67.36)
a <- rep(0, k); a[k] <- 1
gam <- as.vector(Xs %*% XtXi %*% a)
resid <- as.vector(ys - Xs %*% qd)
t0 <- abs(sum(a * qd) - 5 * log10(67.36)) / sqrt(sum(gam^2 * resid^2))
h <- rowSums((Xs %*% XtXi) * Xs)
cat("t0 (HC0, fixed Planck value) =", t0, "  h_max =", max(h), "  1-2h_max =", 1 - 2 * max(h), "\n")
z <- certified(Xs, a, t0)
cat("certified bound applicable:", is.null(z$inapplicable), "\n")
cg <- cumsum(sort(gam^2, decreasing = TRUE)) / sum(gam^2)
cat("share of contrast variance in top 5 / 20 / 100 rows:", round(cg[c(5, 20, 100)], 3), "\n")
top <- order(h, decreasing = TRUE)[1:6]
for (i in top) cat(sprintf("  h=%.3f row %d, nonzero cols {%s}, y=%.3f, sd=%.3f\n",
  h[i], i, paste(which(abs(Xs[i, ]) > 1e-6), collapse = ","), y[i], 1 / w[i]))
