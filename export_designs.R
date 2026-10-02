# export_designs.R -- export X, y, a, v0 and the HC0 statistic t0 for all 17 exhibit rows
# (same construction as cantelli_bounds.R) to mc_search/designs/<name>_{X,y,a,meta}.csv
suppressMessages(source("cantelli_bounds.R"))   # builds `rows` (17 designs) and cantelli_results.csv
for (nm in names(rows)) { r <- rows[[nm]]; X <- as.matrix(r$X); y <- r$y; a <- r$a
  XtXi <- solve(crossprod(X)); bh <- XtXi %*% crossprod(X, y); e <- as.vector(y - X %*% bh)
  g <- as.vector(X %*% XtXi %*% a); t0 <- abs(sum(a*bh) - r$v0)/sqrt(sum(g^2*e^2))
  write.csv(X, sprintf("mc_search/designs/%s_X.csv", nm), row.names=FALSE)
  write.csv(data.frame(y=y), sprintf("mc_search/designs/%s_y.csv", nm), row.names=FALSE)
  write.csv(data.frame(a=a), sprintf("mc_search/designs/%s_a.csv", nm), row.names=FALSE)
  write.csv(data.frame(name=nm, n=nrow(X), p=ncol(X), v0=r$v0, t0=t0), sprintf("mc_search/designs/%s_meta.csv", nm), row.names=FALSE)
  cat(sprintf("%-24s n=%5d p=%d t0=%.4f\n", nm, nrow(X), ncol(X), t0)) }
