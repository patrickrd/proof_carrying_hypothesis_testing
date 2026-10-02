# results_v3b.R -- final results table: 17 rows (15 + two creationist tests), with the
# asymptotic Gaussian p (2(1-Phi(t_HC0)), log10) and mixture e-values; creationist rows
# have exact-zero Group B p-values (u > B*sum|gamma|: impossible under the declared bounds).
suppressMessages(source("conservative_bounds.R"))   # rebuilds results_v3.csv (15 rows) + functions
d <- read.csv("results_v3.csv")
## asymptotic column
asym <- function(X,y,a){ t0<-abs(hc0_t(X,y,a)); log10(2)+pnorm(-t0,log.p=TRUE)/log(10) }
al <- c()
for(nm in names(smax)){ D<-designs[[nm]]; al[nm]<-asym(D$X,D$y,D$a) }
dd<-strep_tb; died<-as.numeric(dd$radiologic_6m=="1_Death"); trt<-as.numeric(dd$arm=="Streptomycin")
al["strep"]<-asym(cbind(1,trt),died,c(0,1))
an<-anorexia[anorexia$Treat %in% c("FT","Cont"),]; ya<-an$Postwt-an$Prewt; ft<-as.numeric(an$Treat=="FT")
al["anorexia"]<-asym(cbind(1,ft),ya,c(0,1))
## SH0ES: t_HC0 of the diagonal-weight refit, contrast against the Planck value, as computed by cantelli_bounds.R
cr <- read.csv("cantelli_results.csv"); t_shoes <- cr$t_hc0[cr$dataset=="SH0ES"]
if(length(t_shoes)!=1 || is.na(t_shoes)) stop("run cantelli_bounds.R first: SH0ES t_hc0 not found in cantelli_results.csv")
al["SH0ES"]<- log10(2)+pnorm(-t_shoes,log.p=TRUE)/log(10)   # was the literal 4.86 (the published tension z), fixed 2 Oct 2026
d$asym_l10 <- al[d$dataset]
## creationist rows
v0 <- (1/(6000*(60^2*24*365)))*3.09e19
crow <- function(nm, x, y, df){
  X<-matrix(x,ncol=1); XtXi<-1/sum(x^2); g<-x*XtXi
  bh<-sum(x*y)*XtXi; u<-abs(bh-v0); e<-y-x*bh
  se_cl <- sqrt(sum(e^2)/df*XtXi)
  rep_p <- 2*pt(-u/se_cl, df=df)   # classical t-dist p (Wood's construction)
  t0<-u/sqrt(sum(g^2*e^2))
  z<-certified(X, 1, t0, kappa=3, b3ratio=sqrt(8/pi), cr=0.5)
  na<-min(1, z$bounds$best_unu["bound"])
  # impossibility check and e-values at observed N (= u)
  imposs <- u > 2000*sum(abs(g))
  data.frame(dataset=nm, reported=rep_p, normapx=na, mc=NA,
    hoeffding=0, bernstein=0, bennett_l10=-Inf,
    e_ho=mix_l10E(u,g,500,2000,"hoeff"), e_be=mix_l10E(u,g,500,2000,"bern"),
    e_bn=mix_l10E(u,g,500,2000,"benn"), asym_l10=log10(2)+pnorm(-t0,log.p=TRUE)/log(10),
    impossible=imposs)
}
hb<-designs[["hubble_teach"]]; h29<-designs[["Hubble1929"]]
d$impossible <- FALSE
d <- rbind(d, crow("hubble_creationist", hb$X[,2], hb$y, 21),
              crow("Hubble1929_creationist", h29$X[,2], h29$y, 23))
print(d[,c("dataset","reported","asym_l10","normapx","hoeffding","bernstein","bennett_l10","e_bn","impossible")], digits=3)
write.csv(d,"results_v3b.csv",row.names=FALSE)
cat("written results_v3b.csv\n")

## RR REDESIGN <2026-09-17>: match Herndon-Ash-Pollin WP322 Table 4 (four debt categories,
## 0-30 baseline; our OLS reproduces their printed column: -1.08, -0.99, -2.01 (0.31)).
## Contrast: the >=90 coefficient. Reported p = Gaussian tail implied by their table.
## MC cell: the earlier search used the old two-group design -> not valid here; not rerun.
rr<-read.csv("dataset_story_data/RR-processed.csv"); rr<-rr[!is.na(rr$dRGDP)&!is.na(rr$debtgdp),]
Xr<-cbind(1, as.numeric(rr$debtgdp>=30&rr$debtgdp<60), as.numeric(rr$debtgdp>=60&rr$debtgdp<90),
          as.numeric(rr$debtgdp>=90))
ar<-c(0,0,0,1); yr<-rr$dRGDP
XtXi<-solve(crossprod(Xr)); g<-as.vector(Xr%*%XtXi%*%ar)
u<-abs(sum(ar*(XtXi%*%crossprod(Xr,yr)))); t0<-abs(hc0_t(Xr,yr,ar))
z<-certified(Xr, ar, t0, kappa=3, b3ratio=sqrt(8/pi), cr=0.5)
i<-which(d$dataset=="ReinhartRogoff")
d$reported[i]<-2*pnorm(-2.0055513/0.3132244)   # implied by HAP Table 4 printed values
d$normapx[i]<-min(1, z$bounds$best_unu["bound"]); d$mc[i]<-NA
d$hoeffding[i]<-min(1,2*exp(-u^2/(2*30^2*sum(g^2))))
d$bernstein[i]<-min(1,2*exp(-u^2/(2*(36*sum(g^2)+30*max(abs(g))*u/3))))
d$bennett_l10[i]<-{dd<-abs(g)*30; cc<-abs(g)*36/30; p<-36/936
  K<-function(l) sum(log(p*exp(pmin(l*dd,700))+(1-p)*exp(-l*cc)))
  lam<-optimize(function(l) K(l)-l*u,c(1e-12,200/max(dd)),tol=1e-14)$minimum
  log10(2)+(K(lam)-lam*u)/log(10)}
d$e_ho[i]<-mix_l10E(u,g,6,30,"hoeff"); d$e_be[i]<-mix_l10E(u,g,6,30,"bern"); d$e_bn[i]<-mix_l10E(u,g,6,30,"benn")
d$asym_l10[i]<-log10(2)+pnorm(-t0,log.p=TRUE)/log(10)
print(d[i,],digits=3)
write.csv(d,"results_v3b.csv",row.names=FALSE)
cat("rewritten results_v3b.csv with RR redesign\n")
