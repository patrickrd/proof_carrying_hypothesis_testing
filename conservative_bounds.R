# conservative_bounds.R -- the <2026-09-16> rework (instruction set):
#  * Group B (Hoeffding/Bernstein/Bennett): NEW, very conservative declared bounds
#    (roughly double the earlier s_max; B with a physical/contextual argument), per dataset.
#  * Normal approximation: BEST-CHANCE instantiation for every dataset: equal variances,
#    Gaussian moment ratios (kappa=3, b3=sqrt(8/pi)), best published BE constants, worst
#    case over |r_i| <= sigma/2. (Goal 1: show the route uncompetitive even at its best.)
#  * MC column: NOT recomputed here (goal 2 uses dataset_ceilings.csv, same class).
#  * E-values (option b): MIXTURE over a declared, data-independent grid: for each method,
#    lambda_j = exponent optimiser at target u_j = z_j * scale, z_j = 0.5*1.25^(0:24)
#    (25 geometric points, ~0.5 to 105), both signs, equal weights 1/50. Valid e-value:
#    a convex combination of fixed-lambda e-values. Loss vs the lambda-envelope is at most
#    a factor ~50 plus a small grid-misfit term. Scale = s_max*sqrt(sum gamma^2) for
#    Bernstein/Bennett, B*sqrt(sum gamma^2) for Hoeffding.
# Output: results_v3.csv
suppressMessages(source("symmetric_bounds.R"))   # designs (12 datasets)
suppressMessages(library(medicaldata))
source("dataset_bounds.R")                        # certified(), hc0_t

## NEW conservative declared bounds (response units)
smax <- c(cars=35, hubble_teach=500, Hubble1929=500, Galton_slope0=4.5, Galton_slope1=4.5,
          Boston_nox=10, Mincer_educ=0.9, CardKrueger=18, ReinhartRogoff=6,
          GISTEMP=0.25, Moore=1.5, Chinchilla=0.2)
Bbig <- c(cars=175, hubble_teach=2000, Hubble1929=2000, Galton_slope0=18, Galton_slope1=18,
          Boston_nox=45, Mincer_educ=3.6, CardKrueger=70, ReinhartRogoff=30,
          GISTEMP=1.0, Moore=6, Chinchilla=1.0)

hoeff <- function(u,g,B) min(1, 2*exp(-u^2/(2*B^2*sum(g^2))))
bern  <- function(u,g,s,B) min(1, 2*exp(-u^2/(2*(s^2*sum(g^2)+B*max(abs(g))*u/3))))
bennett_l10 <- function(g,u,s,B){
  d<-abs(g)*B; cc<-abs(g)*s^2/B; p<-s^2/(B^2+s^2); if(length(p)==1) p<-rep(p,length(g))
  keep<-abs(g)>0; d<-d[keep]; cc<-cc[keep]; p<-p[keep]
  K<-function(l) sum(log(p*exp(pmin(l*d,700))+(1-p)*exp(-l*cc)))
  lam<-optimize(function(l) K(l)-l*u, c(1e-12,200/max(d)),tol=1e-14)$minimum
  min(0, log10(2)+(K(lam)-lam*u)/log(10)) }

## mixture e-values (log10). exponent psi per method; lambda_j data-independent.
zgrid <- 0.5*1.25^(0:24)
mix_l10E <- function(u, g, s, B, method){
  Vs <- sqrt(sum(g^2))
  if(method=="hoeff"){ scale<-B*Vs
    psi<-function(l) l^2*B^2*sum(g^2)/2
    lopt<-function(uj) uj/(B^2*sum(g^2)) }
  if(method=="bern"){ scale<-max(s)*Vs; M<-B*max(abs(g))
    psi<-function(l) l^2*sum((g*s)^2)/(2*(1-pmin(l*M/3,0.999)))
    lopt<-function(uj) uj/(sum((g*s)^2)+M*uj/3) }
  if(method=="benn"){ scale<-max(s)*Vs
    d<-abs(g)*B; cc<-abs(g)*s^2/B; p<-s^2/(B^2+s^2); if(length(p)==1) p<-rep(p,length(g))
    keep<-abs(g)>0; d<-d[keep]; cc<-cc[keep]; p<-p[keep]
    psi<-function(l) sum(log(p*exp(pmin(l*d,700))+(1-p)*exp(-l*cc)))
    lopt<-function(uj) optimize(function(l) psi(l)-l*uj, c(1e-12,200/max(d)),tol=1e-12)$minimum }
  lams <- vapply(zgrid*scale, lopt, 0)
  # log-sum-exp over 50 components (both signs), weights 1/50
  le <- c(lams*u - vapply(lams,psi,0), -lams*u - vapply(lams,psi,0))
  m <- max(le)
  (m + log(sum(exp(le-m))) - log(50))/log(10) }

row_out <- function(nm, X, y, a, s, B, reported, mc){
  XtXi<-solve(crossprod(X)); g<-as.vector(X%*%XtXi%*%a)
  u<-abs(sum(a*(XtXi%*%crossprod(X,y)))); t0<-abs(hc0_t(X,y,a))
  z<-certified(X, a, t0, kappa=3, b3ratio=sqrt(8/pi), cr=0.5)
  na<-if(isTRUE(z$inapplicable)) NA else min(1, z$bounds$best_unu["bound"])
  data.frame(dataset=nm, reported=reported, normapx=na, mc=mc,
    hoeffding=hoeff(u,g,B), bernstein=bern(u,g,max(s),B), bennett_l10=bennett_l10(g,u,s,B),
    e_ho=mix_l10E(u,g,s,B,"hoeff"), e_be=mix_l10E(u,g,s,B,"bern"), e_bn=mix_l10E(u,g,s,B,"benn"))
}

## MC column: goal-2 class (equal variances, Gaussian ratios, |r|<=sigma/2) from
## dataset_ceilings.csv: max over the two searched variants (both lie inside the class).
mcv <- c(cars=4.45e-5, hubble_teach=1.75e-6, Hubble1929=1.02e-2, Galton_slope0=NA,
  Galton_slope1=NA, Boston_nox=5.27e-5, Mincer_educ=NA, CardKrueger=4.53e-2,
  ReinhartRogoff=3.71e-4, GISTEMP=NA, Moore=NA, Chinchilla=NA)  # NA = below MC resolution
rep_p<-setNames(rep(NA_real_, 12), c("cars", "hubble_teach", "Hubble1929", "Galton_slope0", "Galton_slope1", "Boston_nox", "Mincer_educ", "CardKrueger", "ReinhartRogoff", "GISTEMP", "Moore", "Chinchilla"))  # reported p-values are not computed here; see README

out<-data.frame()
for(nm in names(smax)){ D<-designs[[nm]]
  out<-rbind(out, row_out(nm, D$X, D$y, D$a, smax[nm], Bbig[nm], rep_p[nm], mcv[nm])) }
## strep (provable 1/2, 1) and anorexia (conservative 15, 45); MC missing (not run)
d<-strep_tb; died<-as.numeric(d$radiologic_6m=="1_Death"); trt<-as.numeric(d$arm=="Streptomycin")
out<-rbind(out, row_out("strep", cbind(1,trt), died, c(0,1), 0.5, 1, NA, NA))
an<-anorexia[anorexia$Treat %in% c("FT","Cont"),]; ya<-an$Postwt-an$Prewt
ft<-as.numeric(an$Treat=="FT")
out<-rbind(out, row_out("anorexia", cbind(1,ft), ya, c(0,1), 15, 45, NA, NA))
## SH0ES: per-observation conservative scales s_i = 1.5, B_i = 6 (quoted-error multiples)
scr <- path.expand("~/temp/shoes_data/")
read_fits <- function(f){ con<-file(f,"rb"); hdr<-character(0)
  repeat{ block<-readChar(con,2880,useBytes=TRUE)
    cards<-substring(block,seq(1,2801,80),seq(80,2880,80)); hdr<-c(hdr,cards)
    if(any(grepl("^END *$",cards))) break }
  gv<-function(k){ x<-hdr[grepl(paste0("^",k," *="),hdr)][1]
    if(is.na(x)) return(NA_real_)
    as.numeric(trimws(strsplit(strsplit(x,"=")[[1]][2],"/")[[1]][1])) }
  n1<-gv("NAXIS1"); n2<-if(gv("NAXIS")>=2) gv("NAXIS2") else 1
  dat<-readBin(con,"numeric",n=n1*n2,size=4,endian="big"); close(con)
  matrix(dat,nrow=n2,ncol=n1,byrow=TRUE) }
yv<-as.vector(read_fits(paste0(scr,"ally.fits")))
L<-read_fits(paste0(scr,"alll.fits")); if(nrow(L)!=length(yv)) L<-t(L)
Cv<-read_fits(paste0(scr,"allc.fits")); w<-1/sqrt(diag(Cv)); keepc<-setdiff(1:47,45)
Xs<-(L*w)[,keepc]; ys<-yv*w; XtXi<-solve(crossprod(Xs)); k<-ncol(Xs)
qd<-qr.solve(Xs,ys); a<-rep(0,k); a[k]<-1
g<-as.vector(Xs%*%XtXi%*%a); u<-abs(sum(a*qd)-5*log10(67.36))
sv<-rep(1.5,nrow(Xs)); Bv<-6
out<-rbind(out, data.frame(dataset="SH0ES", reported=5.7e-7, normapx=NA, mc=NA,
  hoeffding=hoeff(u,g,6), bernstein=bern(u,g,1.5,6), bennett_l10=bennett_l10(g,u,sv,6),
  e_ho=mix_l10E(u,g,sv,6,"hoeff"), e_be=mix_l10E(u,g,sv,6,"bern"), e_bn=mix_l10E(u,g,sv,6,"benn")))
print(out, digits=3)
write.csv(out,"results_v3.csv",row.names=FALSE)
cat("written results_v3.csv\n")
