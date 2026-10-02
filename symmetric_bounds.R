# symmetric_bounds.R -- the sign-symmetry certificate (symmetric_case.tex, Theorem "sym")
# evaluated on every dataset in the exhibit, well-specified and misspecified, homogeneous
# magnitude profile (m_i = 1). Bound (conditional on m):
#   P(|T| >= t) <= 2 exp(-c^2 t^2 / 2)                              [numerator, Efron/Hoeffding]
#                + [r != 0] exp(-alpha^2 tau^2 / (8 S_lin^2))       [linear sign term, Hoeffding]
#                + min{1, 4 S_pair^2 / ((1-alpha)^2 tau^2)}         [paired-sign term, Chebyshev]
#   tau = (1-c^2) V^2 + rho^2 - 2 Q0,  optimised over c in (0,1), alpha in [0,1].
# Statistic: HC2-studentised contrast (the certificate's native studentisation).
# Misspecification: r = (I-H)v, v = squared tested predictor (a plausible omitted curvature),
# scaled to max|r_i| = 1/2 (= sigma/2 in m_i=1 units), matching the BE exhibit's allowance.
# For a design whose only non-intercept regressor is a group indicator, the mean is a function
# of that indicator and is representable, so r = 0 is forced: well-spec = misspec.
suppressMessages({library(MASS); library(gamair); library(HistData); library(wooldridge)})
dd <- "dataset_story_data/"

designs <- list()
add <- function(name, X, y, a, curv) designs[[name]] <<- list(X=as.matrix(X), y=y, a=a, curv=curv)
data(cars); add("cars", cbind(1,cars$speed), cars$dist, c(0,1), cars$speed^2)
data(hubble); hb <- hubble[-c(3,15),]; add("hubble_teach", cbind(1,hb$x), hb$y, c(0,1), hb$x^2)
h29 <- read.csv(paste0(dd,"hubble1929.csv")); add("Hubble1929", cbind(1,h29$r), h29$v, c(0,1), h29$r^2)
data(Galton); add("Galton_slope0", cbind(1,Galton$parent), Galton$child, c(0,1), Galton$parent^2)
add("Galton_slope1", cbind(1,Galton$parent), Galton$child-Galton$parent, c(0,1), Galton$parent^2)
data(Boston); Xb <- as.matrix(cbind(1, Boston[,setdiff(names(Boston),"medv")]))
add("Boston_nox", Xb, Boston$medv, as.numeric(colnames(Xb)=="nox"), Boston$nox^2)
data(wage1); Xw <- as.matrix(cbind(1, wage1[,c("educ","exper","tenure")]))
add("Mincer_educ", Xw, wage1$lwage, c(0,1,0,0), wage1$educ^2)
ck <- read.fwf(paste0(dd,"public.dat"),
  widths=c(3,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,2,-1,5,-1,5,-1,5,-1,5,-1,5,
           -1,5,-1,1,-1,5,-1,1,-1,5,-1,5,-1,5,-1,5,-1,5,-1,2,-1,2,-1,1,-1,1,-1,6,-1,2,-1,5,
           -1,5,-1,5,-1,5,-1,5,-1,5,-1,1,-1,1,-1,5,-1,5,-1,5,-1,5,-1,5,-1,2,-1,2),
  strip.white=TRUE, na.strings=".")
f1 <- ck[,12]+0.5*ck[,13]+ck[,14]; f2 <- ck[,32]+0.5*ck[,33]+ck[,34]; kp <- !is.na(f1)&!is.na(f2)
add("CardKrueger", cbind(1, ck[kp,4]), f2[kp]-f1[kp], c(0,1), NULL)   # group indicator: r=0 forced
rr <- read.csv(paste0(dd,"RR-processed.csv")); rr <- rr[!is.na(rr$dRGDP)&!is.na(rr$debtgdp),]
add("ReinhartRogoff", cbind(1, as.numeric(rr$debtgdp>=90)), rr$dRGDP, c(0,1), NULL)  # indicator: r=0
g <- read.csv(paste0(dd,"gistemp_global.csv"), skip=1); g <- g[g$Year>=1970&g$Year<=2025,]
add("GISTEMP", cbind(1,g$Year), as.numeric(g$J.D), c(0,1), (g$Year-mean(g$Year))^2)
m <- read.csv(paste0(dd,"moore.csv")); names(m)[4]<-"tr"
add("Moore", cbind(1,m$Year), log2(m$tr), c(0,1), (m$Year-mean(m$Year))^2)
ch <- read.csv(paste0(dd,"chinchilla_epoch.csv")); Nn<-ch$Model.Size; Dd<-ch$Training.FLOP/(6*Nn)
add("Chinchilla", cbind(1,log(Nn),log(Dd)), log(ch$loss-1.8172), c(0,0,1), log(Dd)^2)

## observed HC2-studentised statistic
obs_t_hc2 <- function(X,y,a){ XtXi<-solve(crossprod(X)); bh<-XtXi%*%crossprod(X,y)
  H<-X%*%XtXi%*%t(X); h<-diag(H); e<-as.vector(y-X%*%bh); w<-as.vector(X%*%XtXi%*%a)
  abs(sum(a*bh)/sqrt(sum(w^2*e^2/(1-h)))) }

## the certificate at homogeneous profile m=1
sym_cert <- function(X, a, t, curv=NULL, misspec=FALSE) {
  n<-nrow(X); XtXi<-solve(crossprod(X)); w<-as.vector(X%*%XtXi%*%a)
  H<-X%*%XtXi%*%t(X); h<-diag(H); IH<-diag(n)-H
  V2<-sum(w^2); Q0<-sum(w^2*h)
  offsq <- (H*H); diag(offsq)<-0                     # H_ij^2 for i!=j
  wij <- outer(w^2,w^2,`+`)                           # (w_i^2 + w_j^2)
  Spair2 <- sum(offsq * wij^2)/2                      # sum_{i<j} H_ij^2 (w_i^2+w_j^2)^2
  if (misspec && !is.null(curv)) {
    r <- as.vector(IH %*% curv); r <- r/max(abs(r))*0.5      # max|r_i| = 1/2
    rho2 <- sum(w^2*r^2); u <- as.vector(IH %*% (w^2*r)); Slin2 <- sum(u^2)
  } else { r<-rep(0,n); rho2<-0; Slin2<-0 }
  cs <- seq(0.01,0.98,by=0.01); als <- if(rho2>0) seq(0,0.99,by=0.02) else 0
  best<-1
  for(c2 in cs){ tau<-(1-c2)*V2+rho2-2*Q0; if(tau<=0) next
    num<-2*exp(-c2*t^2/2)
    for(al in als){
      lin <- if(Slin2>0 && al>0) exp(-al^2*tau^2/(8*Slin2)) else if(al>0) 0 else 0
      pair<- min(1, 4*Spair2/((1-al)^2*tau^2))
      tot<-num+lin+pair; if(tot<best) best<-tot } }
  list(cert=min(1,best), Q0V2=Q0/V2, Spair2V4=Spair2/V2^2, rho2V2=rho2/V2)
}

## reported p and BE well-spec/misspec (from the exhibit, for comparison)
reported <- c(cars=1.5e-12,hubble_teach=3.0e-10,Hubble1929=4.5e-6,Galton_slope0=1.7e-49,
 Galton_slope1=3.4e-17,Boston_nox=4.3e-6,Mincer_educ=8.8e-32,CardKrueger=1.8e-2,
 ReinhartRogoff=4.2e-6,GISTEMP=1.2e-29,Moore=1.9e-42,Chinchilla=1.9e-121)
be_well <- c(cars=0.40,hubble_teach=0.89,Hubble1929=1,Galton_slope0=0.020,Galton_slope1=0.038,
 Boston_nox=0.80,Mincer_educ=0.063,CardKrueger=0.42,ReinhartRogoff=0.23,GISTEMP=0.14,
 Moore=0.22,Chinchilla=0.092)
be_mis <- c(cars=0.89,hubble_teach=1,Hubble1929=1,Galton_slope0=0.043,Galton_slope1=0.071,
 Boston_nox=1,Mincer_educ=0.13,CardKrueger=0.60,ReinhartRogoff=0.33,GISTEMP=0.36,
 Moore=0.68,Chinchilla=0.23)

cat(sprintf("%-15s %6s | %-9s %-7s %-7s | %-8s %-8s\n",
  "dataset","t_HC2","reported","BE_well","BE_mis","sym_well","sym_mis"))
out <- data.frame()
for(nm in names(designs)){ D<-designs[[nm]]; t<-obs_t_hc2(D$X,D$y,D$a)
  sw<-sym_cert(D$X,D$a,t,D$curv,FALSE)$cert
  sm<-if(is.null(D$curv)) sw else sym_cert(D$X,D$a,t,D$curv,TRUE)$cert
  cat(sprintf("%-15s %6.2f | %-9.1e %-7.2g %-7.2g | %-8.3g %-8.3g\n",
    nm, t, reported[nm], be_well[nm], be_mis[nm], sw, sm))
  out<-rbind(out,data.frame(dataset=nm,t_hc2=t,reported=reported[nm],be_well=be_well[nm],
    be_mis=be_mis[nm],sym_well=sw,sym_mis=sm)) }
write.csv(out,"symmetric_bounds.csv",row.names=FALSE)
