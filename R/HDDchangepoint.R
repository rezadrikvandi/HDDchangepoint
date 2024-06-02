# HDDchangepoint - High dimensional change point detection, written by Reza Drikvandi <reza.drikvandi@durham.ac.uk>

#---------------------------------------------------------------------------------------------------
#' This function uses the new dissimilarity measure d(Xi,Xj) to calculate the distance matrix of given data
#' @param data    a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @return   the distance matrix of data
#' @export

dist1 <- function(data)
{
  N=nrow(data)
  px=ncol(data)
  Newzbar=matrix(0,nrow=N,ncol=N)
  con=1/(N-2)
  kk=1
  for (ix in 1:(N-1))
  { xx=data[ix,];      mux=sum(xx)/px;   vx=sqrt(sum((xx-mux)^2)/px);
  for (iy in (ix+1):N)
  { yy=data[iy,];     muy=sum(yy)/px;   vy=sqrt(sum((yy-muy)^2)/px);
  part=0
  for (it in 1:N)  if ((it!=ix) & (it!=iy)) {
    zz=data[it,]
    muz=sum(zz)/px
    vz=sqrt(sum((zz-muz)^2)/px)
    dxz=sqrt(((mux-muz)^2+(vx-vz)^2))
    dyz=sqrt(((muy-muz)^2+(vy-vz)^2))
    part=part+abs(dxz-dyz)
  }
  Newzbar[ix,iy]=con*part
  Newzbar[iy,ix]=Newzbar[ix,iy]
  kk=kk+1
  }
  }
  return(Newzbar)
}

#---------------------------------------------------------------------------------------------------
#' This function uses the new dissimilarity measure d(Xi,Xj) to calculate the distance matrix of given data
#' @param data    a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @return   the distance matrix of data
#' @export

dist2 <- function(data)
{
  N=nrow(data)
  d=ncol(data)
  R0=matrix(0,nrow=N,ncol=N)
  con=1/((N-2))
  ipdmat <- (as.matrix(dist(data))/sqrt(d))
  for (ix in 1:N)
  {
    for (iy in ix:N)
    {
      part1=ipdmat[ix,]
      p1=part1[-ix]
      iy1=iy-1
      Q1=p1[-iy1]
      part2=ipdmat[iy,]
      p2=part2[-ix]
      Q2=p2[-iy1]
      R0[ix,iy]=(con*sum(abs(Q1-Q2)))
      R0[iy,ix]= R0[ix,iy]
    }
  }
  return(R0)
}

#---------------------------------------------------------------------------------------------------
#' This function calculates the proposed test statistic T for given data and dissimilarity measure
#' @param data    a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN     a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @return  the change point estimate together with the test statistics T and W
#' @export

test_statistic <- function(data,FUN=dist1){
  nn <- nrow(data)
  d <- ncol(data)
  distance_matrix <- as.matrix(FUN(data))
  if(identical(FUN,dist))
  {
    #just for the modified Euclidean distance as it requires dividing by sqrt(d)
    distance_matrix <- distance_matrix/sqrt(d)
  }
  diffdis <- matrix(0,nn,nn)
  for(i in 1:nn) {
    for (j in 2:nn) {
      diffdis[i,j] <- abs(distance_matrix[i,j]-distance_matrix[i,j-1])
    }
  }
  colsumD <- colSums(diffdis)/nn
  changepoint_estimate <- which(colsumD==max(colsumD))[1]
  distance_n <- numeric(nn)
  wt <- numeric(nn)
  if(changepoint_estimate == nn | changepoint_estimate <= 2){
    Tstat <- 0
    Wstat <- 0
  } else{for(i in 1:nn){
    dis_before <- distance_matrix[i,1:(changepoint_estimate-1)]
    dis_after <- distance_matrix[i,(changepoint_estimate):nn]
    sum_w <- 0
    sum_t <- 0
    for(j in 1:(changepoint_estimate-1)){
      for(jj in (changepoint_estimate):nn){
        sum_t <- sum_t + (distance_matrix[i,j]-distance_matrix[i,jj])^2
        sum_w <- sum_w + (mean(data[i,])-mean(data[j,]))^2+(sd(data[i,])-sd(data[j,]))^2+
          (mean(data[i,])-mean(data[jj,]))^2+(sd(data[i,])-sd(data[jj,]))^2
      }
    }
    distance_n[i] <- sum_t/(length(dis_before)*length(dis_after))
    wt[i] <- sum_w/(length(dis_before)*length(dis_after))
  }
    Tstat <- mean(distance_n)
    Wstat <- mean(wt)
  }
  return(list(changepoint_estimate,Tstat,Wstat))
}

#---------------------------------------------------------------------------------------------------
#' This function runs the proposed algorithm for single change point detection in high dimensional data
#' @param data         a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN          a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @param test         either asymptotic or permutation test, default is the asymptotic test
#' @param npermut      number of permutations for permutation test, default is 200
#' @param siglevel     the significance level, default is 0.05
#' @return   the change point candidate and whether it is significant or not (1 significant, 0 not significant),
#'           as well as the p-value of the test for change point
#' @export

test_single_changepoint <- function(data,FUN=dist1,test="asymptotic",npermut=200,siglevel=0.05){
  changepoint_candidate=NULL
  nn <- nrow(data)
  d <- ncol(data)
  changepoint_stat <- test_statistic(data=data,FUN=FUN)
  changepoint_estimate <- changepoint_stat[[1]]
  Tstat <- changepoint_stat[[2]]
  Wstat <- changepoint_stat[[3]]
  if(test=="permutation"){
    #Permutation test for testing significance of the change point estimate
    up <- npermut*(1-siglevel)
    Tstat_permut <-rep(NULL, npermut)
    for (perm in 1:npermut)
    {
      permu_without <- 1:(nn)
      if(changepoint_estimate>2){
        permu_without_before <- permu_without[1:(changepoint_estimate-2)]
        permu_without_after <- permu_without[(changepoint_estimate):nn]
        permu_without <- c(permu_without_before,permu_without_after)
        permu_without <- sample(permu_without)
        permu_with <- insert(permu_without, ats=changepoint_estimate-1, values=changepoint_estimate-1)
        samplepermut_max <- data[permu_with, ]
      } else if(changepoint_estimate==2){
        permu_without_after <- permu_without[(changepoint_estimate):nn]
        permu_without <- c(permu_without_after)
        permu_without <- sample(permu_without)
        permu_with <- insert(permu_without, ats=changepoint_estimate-1, values=changepoint_estimate-1)
        samplepermut_max <- data[permu_with, ]
      } else{
        samplepermut_max <- data[permu_with, ]
      }
      changepoint_stat_per <- test_statistic(data=samplepermut_max,FUN=FUN)
      Tstat_permut[perm] <- changepoint_stat_per[[2]]
    }
    Tstat_permut_up = sort(Tstat_permut)[up]
    if(Tstat>Tstat_permut_up){
      whether_changepoint <- 1
      changepoint_candidate <- changepoint_estimate
      p_value <- sum(Tstat_permut>Tstat)/npermut
    } else{
      whether_changepoint <- 0
      changepoint_candidate <- NA
      p_value <- NA
    }
  } else if(test=="asymptotic"){
    #Asymptotic test for testing significance of the change point estimate
    sum_m1 <- 0
    sum_m2 <- 0
    sum_c1 <- 0
    sum_c2 <- 0
    sum_c3 <- 0
    sum_c4 <- 0
    for(i in 1:nn){
      vi <- (((d-1)/d)*(sd(data[i,]))^2)/d
      vi_star <- (sum(((data[i,]-mean(data[i,])))^4)/d^2)/(4*((d-1)/d)*(sd(data[i,])^2))-(d*vi^2)/(4*((d-1)/d)*(sd(data[i,])^2))
      for(j in 1:(changepoint_estimate-1)){
        vj <- (((d-1)/d)*(sd(data[j,]))^2)/d
        vj_star <- (sum(((data[j,]-mean(data[j,])))^4)/d^2)/(4*((d-1)/d)*(sd(data[j,])^2))-(d*vj^2)/(4*((d-1)/d)*(sd(data[j,])^2))
        sum_m1 <- sum_m1+(vi+vj+vi_star+vj_star)
        for(k in 1:nn){
          for(l in 1:(changepoint_estimate-1)){
            if(i!=j & k!=l & i==k & j==l){sum_c1 <- sum_c1 +2*((vi+vj)^2+(vi_star+vj_star)^2)
            } else if(i!=j & k!=l & i==k & j!=l){sum_c1 <- sum_c1 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if(i!=j & k!=l & i!=k & j==l){sum_c1 <- sum_c1 +((vj+vj)^2+(vj_star+vj_star)^2)/2
            } else if(i!=j & k!=l & i==l & j==k){sum_c1 <- sum_c1 +2*((vi+vj)^2+(vi_star+vj_star)^2)
            } else if(i!=j & k!=l & i==l & j!=k){sum_c1 <- sum_c1 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if(i!=j & k!=l & i!=l & j==k){sum_c1 <- sum_c1 +((vj+vj)^2+(vj_star+vj_star)^2)/2
            } else {sum_c1 <- sum_c1 +0
            }
          }
          for(ll in (changepoint_estimate):nn){
            if(i!=j & k!=ll & i==k & j==ll){sum_c2 <- sum_c2 +2*((vi+vj)^2+(vi_star+vj_star)^2)
            } else if(i!=j & k!=ll & i==k & j!=ll){sum_c2 <- sum_c2 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if(i!=j & k!=ll & i!=k & j==ll){sum_c2 <- sum_c2 +((vj+vj)^2+(vj_star+vj_star)^2)/2
            } else if(i!=j & k!=ll & i==ll & j==k){sum_c2 <- sum_c2 +2*((vi+vj)^2+(vi_star+vj_star)^2)
            } else if(i!=j & k!=ll & i==ll & j!=k){sum_c2 <- sum_c2 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if(i!=j & k!=ll & i!=ll & j==k){sum_c2 <- sum_c2 +((vj+vj)^2+(vj_star+vj_star)^2)/2
            } else {sum_c2 <- sum_c2+0
            }
          }
        }
      }
      for(jj in (changepoint_estimate):nn){
        vjj <- (((d-1)/d)*(sd(data[jj,]))^2)/d
        vjj_star <- (sum(((data[jj,]-mean(data[jj,])))^4)/d^2)/(4*((d-1)/d)*(sd(data[jj,])^2))-(d*vjj^2)/(4*((d-1)/d)*(sd(data[jj,])^2))
        sum_m2 <- sum_m2+(vi+vjj+vi_star+vjj_star)
        for(k in 1:nn){
          for(l in 1:(changepoint_estimate-1)){
            if(i!=jj & k!=l & i==k & jj==l){sum_c3 <- sum_c3 +2*((vi+vjj)^2+(vi_star+vjj_star)^2)
            } else if(i!=jj & k!=l & i==k & jj!=l){sum_c3 <- sum_c3 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if(i!=jj & k!=l & i!=k & jj==l){sum_c3 <- sum_c3 +((vjj+vjj)^2+(vjj_star+vjj_star)^2)/2
            } else if(i!=jj & k!=l & i==l & jj==k){sum_c3 <- sum_c3 +2*((vi+vjj)^2+(vi_star+vjj_star)^2)
            } else if(i!=jj & k!=l & i==l & jj!=k){sum_c3 <- sum_c3 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if(i!=jj & k!=l & i!=l & jj==k){sum_c3 <- sum_c3 +((vjj+vjj)^2+(vjj_star+vjj_star)^2)/2
            } else {sum_c3 <- sum_c3 +0
            }
          }
          for(ll in (changepoint_estimate):nn){
            if(i!=jj & k!=ll & i==k & jj==ll){sum_c4 <- sum_c4 +2*((vi+vjj)^2+(vi_star+vjj_star)^2)
            } else if(i!=jj & k!=ll & i==k & jj!=ll){sum_c4 <- sum_c4 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if(i!=jj & k!=ll & i!=k & jj==ll){sum_c4 <- sum_c4 +((vjj+vjj)^2+(vjj_star+vjj_star)^2)/2
            } else if(i!=jj & k!=ll & i==ll & jj==k){sum_c4 <- sum_c4 +2*((vi+vjj)^2+(vi_star+vjj_star)^2)
            } else if(i!=jj & k!=ll & i==ll & jj!=k){sum_c4 <- sum_c4 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if(i!=jj & k!=ll & i!=ll & jj==k){sum_c4 <- sum_c4 +((vjj+vjj)^2+(vjj_star+vjj_star)^2)/2
            } else {sum_c4 <- sum_c4 +0
            }
          }
        }
      }
    }
    sum_m1 <- sum_m1*length((changepoint_estimate):nn)
    sum_m2 <- sum_m2*length(1:(changepoint_estimate-1))
    sum_m <- sum_m1+sum_m2
    sum_c1 <- sum_c1*length((changepoint_estimate):nn)*length((changepoint_estimate):nn)
    sum_c2 <- sum_c2*length(1:(changepoint_estimate-1))*length((changepoint_estimate):nn)
    sum_c3 <- sum_c3*length(1:(changepoint_estimate-1))*length((changepoint_estimate):nn)
    sum_c4 <- sum_c4*length(1:(changepoint_estimate-1))*length(1:(changepoint_estimate-1))
    sum_c <- sum_c1+sum_c2+sum_c3+sum_c4
    length_delta_bef <- length(1:(changepoint_estimate-1))
    length_delta_aft <- length((changepoint_estimate):nn)
    Wstat_standardised <- (nn*length_delta_bef*length_delta_aft)*(Wstat-sum_m/(nn*length_delta_bef*length_delta_aft))/sqrt(sum_c)
    if(abs(Wstat_standardised)>=qnorm(1-siglevel/2)){
      whether_changepoint <- 1
      changepoint_candidate <- changepoint_estimate
      p_value <- 2*min(1-pnorm(Wstat_standardised),pnorm(Wstat_standardised))
    } else{
      whether_changepoint <- 0
      changepoint_candidate <- NA
      p_value <- NA
    }
  }
  return(list(changepoint_candidate,whether_changepoint,p_value))
}

#---------------------------------------------------------------------------------------------------
#' This is the main function that runs the proposed algorithm for multiple change point detection in high dimensional data
#' @param data          a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN           a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @param test          either asymptotic or permutation test, default is the asymptotic test
#' @param npermut       number of permutations for permutation test, default is 200
#' @param siglevel      the significance level, default is 0.05
#' @param minsegmlength    minimum segment length for recursive binary segmentation, default is 10
#' @return   the list of detected significant change points and the corresponding p-values
#' @export

multiple_changepoint_detection <- function(data,FUN=dist1,minsegmlength=10,test="asymptotic",npermut=200,siglevel=0.05){
  if(is.vector(data) & !is.list(data)){
    print("dimension of data must be more than 1 as this method is for multivariate data")
    noerror <- options(show.error.messages=FALSE)
    on.exit(options(noerror))
    break
  }
  if(ncol(data)==1){
    print("dimension of data must be more than 1 as this method is for multivariate data")
    noerror <- options(show.error.messages=FALSE)
    on.exit(options(noerror))
    break
  }
  changepoint_all <- NA
  pvalue_all <- NA
  length_data <- nrow(data)
  while(length_data>minsegmlength){
    call_changepoint_test <- test_single_changepoint(data=data,FUN=FUN,test=test,npermut=npermut,siglevel=siglevel)
    changepoint <- call_changepoint_test[[1]]
    is_changepoint <- call_changepoint_test[[2]]
    pvalue <- call_changepoint_test[[3]]
    nn_split <- nrow(data)
    if(is_changepoint==1 & changepoint>2 & changepoint<nn_split-2){
      data_before <- data[1:(changepoint-1),]
      data_after <- data[(changepoint+1):nn_split,]
      changepoint_bef <- multiple_changepoint_detection(data=data_before,FUN=FUN,minsegmlength=minsegmlength,test=test,npermut=npermut,siglevel=siglevel)
      changepoint_before <- changepoint_bef[[1]]
      pvalue_before <- changepoint_bef[[2]]
      changepoint_aft <- multiple_changepoint_detection(data=data_after,FUN=FUN,minsegmlength=minsegmlength,test=test,npermut=npermut,siglevel=siglevel)
      changepoint_after <- changepoint_aft[[1]]+changepoint
      pvalue_after <- changepoint_aft[[2]]
      changepoint_all <- c(changepoint,changepoint_before,changepoint_after)
      pvalue_all <- c(pvalue,pvalue_before,pvalue_after)
      changepoint_all <- changepoint_all[!is.na(changepoint_all)]
      pvalue_all <- pvalue_all[!is.na(pvalue_all)]
      pvalue_all <- pvalue_all[order(changepoint_all, decreasing=FALSE)]
      changepoint_all <- sort(changepoint_all)
      return(list("Detected change points"=changepoint_all,"Corresponding p-values"=pvalue_all))
    } else{
      return(list("Detected change points"=NA,"Corresponding p-values"=NA))
      break
    }
  }
  return(list("Detected change points"=changepoint_all,"Corresponding p-values"=pvalue_all))
}

#---------------------------------------------------------------------------------------------------
#' This function calculates confidence intervals (CI) for multiple change points in high dimensional data
#' @param data          a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN           a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @param cp_estimate   a vector of change point locations
#' @param npermutCI     number of permutations for permutation-based confidence intervals, default is 100
#' @param siglevel      the significance level, default is 0.05
#' @return   the lower limit and upper limit of confidence intervals for the change point locations
#' @export

CI_changepoint <- function(data,FUN=dist1,cp_estimate,npermutCI=100,siglevel=0.05){
  cp_estimate <- sort(cp_estimate)
  lowerCI_all <- numeric(length(cp_estimate))
  upperCI_all <- numeric(length(cp_estimate))
  for(i in 1:length(cp_estimate))
  {
    b <- ifelse(i==1,1,cp_estimate[i-1])
    e <- ifelse(i==length(cp_estimate),nrow(data),cp_estimate[i+1]-1)
    datai <- data[b:e,]
    changepoint_estimate <- cp_estimate[i]-(b-1)
    nn <- nrow(datai)
    d <- ncol(datai)
    npermut <- npermutCI
    changepoint_estimate_permut <- numeric(npermut)
    for (perm in 1:npermut)
    {
      permu_without <- 1:(nn)
      if(changepoint_estimate>2){
        permu_without_before <- permu_without[1:(changepoint_estimate-2)]
        permu_before <- sample(permu_without_before)
        permu_without_after <- permu_without[(changepoint_estimate):nn]
        permu_after <- sample(permu_without_after)
        permu_without <- c(permu_before,permu_after)
        permu_with <- insert(permu_without, ats=changepoint_estimate-1, values=changepoint_estimate-1)
        samplepermut_max <- datai[permu_with, ]
      } else if(changepoint_estimate==2){
        permu_without_after <- permu_without[(changepoint_estimate):nn]
        permu_without <- c(permu_without_after)
        permu_without <- sample(permu_without)
        permu_with <- insert(permu_without, ats=changepoint_estimate-1, values=changepoint_estimate-1)
        samplepermut_max <- datai[permu_with, ]
      }
      changepoint_estimate_permut[perm] <- test_statistic(data=samplepermut_max,FUN=FUN)[[1]]
    }
    changepoint_estimate_permut_sorted <- sort(changepoint_estimate_permut)
    lowerCI <- cp_estimate[i]-sqrt(sd(changepoint_estimate_permut))*qnorm(1-siglevel/2)
    upperCI <- cp_estimate[i]+sqrt(sd(changepoint_estimate_permut))*qnorm(1-siglevel/2)
    lowerCI <- floor(lowerCI)
    upperCI <- floor(upperCI)
    lowerCI_all[i] <- max(2,lowerCI)
    upperCI_all[i] <- min(nn+(b-1),upperCI)
  }
  return(list("Lower limit CI"=lowerCI_all,"Upper limit CI"=upperCI_all))
}
