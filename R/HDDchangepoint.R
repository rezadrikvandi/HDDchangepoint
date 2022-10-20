# High dimensional change point detection, written by Reza Drikvandi <reza.drikvandi@durham.ac.uk>

#---------------------------------------------------------------------------------------------------
#' This function uses the new dissimilarity measure d(Xi,Xj) to calculate the distance matrix of given data
#' @param data    a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @return   the distance matrix of data
#' @export

delta0 <- function(data)
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
#' This function calculates the proposed test statistic T for given data and dissimilarity measure
#' @param data    a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN     a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @return  the change point estimate together with the test statistics T and W
#' @export

test_statistic <- function(data,FUN=delta0){
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
#' @return   the change point candidate and whether it is significant or not (1 significant, 0 not significant)
#' @export

test_single_changepoint <- function(data,FUN=delta0,test="asymptotic",npermut=200,siglevel=0.05){
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
    } else{
      whether_changepoint <- 0
      changepoint_candidate <- NA
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
      vi_star <- (sum(((data[i,]-mean(data[i,])))^4)/d^2)/(4*((d-1)/d)*(sd(data[i,])^2))
      #vi_star <- ((sum((CJ(data[i,], data[i,])[,2]-CJ(data[i,], data[i,])[,1])^2)/(2*d*(d-1)))^2-(sd(data[i,])^2))/(4*(sd(data[i,])^2))
      for(j in 1:(changepoint_estimate-1)){
        vj <- (((d-1)/d)*(sd(data[j,]))^2)/d
        vj_star <- (sum(((data[j,]-mean(data[j,])))^4)/d^2)/(4*((d-1)/d)*(sd(data[j,])^2))
        sum_m1 <- sum_m1+(vi+vj+vi_star+vj_star)
        for(k in 1:nn){
          for(l in 1:(changepoint_estimate-1)){
            if(i==j | k==l){sum_c1 <- sum_c1 +0
            } else if((i==k & j==l)|(i==l & j==k)){sum_c1 <- sum_c1 +2*((vi+vj)^2+(vi_star+vj_star)^2)
            } else if((i==k & j!=l)|(i==l & j!=k)){sum_c1 <- sum_c1 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if((i!=k & j==l)|(i!=l & j==k)){sum_c1 <- sum_c1 +((vj+vj)^2+(vj_star+vj_star)^2)/2
            }
          }
          for(ll in (changepoint_estimate):nn){
            if(i==j | k==ll){sum_c2 <- sum_c2 +0
            } else if((i==k & j==ll)|(i==ll & j==k)){sum_c2 <- sum_c2 +2*((vi+vj)^2+(vi_star+vj_star)^2)
            } else if((i==k & j!=ll)|(i==ll & j!=k)){sum_c2 <- sum_c2 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if((i!=k & j==ll)|(i!=ll & j==k)){sum_c2 <- sum_c2 +((vj+vj)^2+(vj_star+vj_star)^2)/2
            }
          }
        }
      }
      for(jj in (changepoint_estimate):nn){
        vjj <- (((d-1)/d)*(sd(data[jj,]))^2)/d
        vjj_star <- (sum(((data[jj,]-mean(data[jj,])))^4)/d^2)/(4*((d-1)/d)*(sd(data[jj,])^2))
        sum_m2 <- sum_m2+(vi+vjj+vi_star+vjj_star)
        for(k in 1:nn){
          for(l in 1:(changepoint_estimate-1)){
            if(i==jj | k==l){sum_c3 <- sum_c3 +0
            } else if((i==k & jj==l)|(i==l & jj==k)){sum_c3 <- sum_c3 +2*((vi+vjj)^2+(vi_star+vjj_star)^2)
            } else if((i==k & jj!=l)|(i==l & jj!=k)){sum_c3 <- sum_c3 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if((i!=k & jj==l)|(i!=l & jj==k)){sum_c3 <- sum_c3 +((vjj+vjj)^2+(vjj_star+vjj_star)^2)/2
            }
          }
          for(ll in (changepoint_estimate):nn){
            if(i==jj | k==ll){sum_c4 <- sum_c4 +0
            } else if((i==k & jj==ll)|(i==ll & jj==k)){sum_c4 <- sum_c4 +2*((vi+vjj)^2+(vi_star+vjj_star)^2)
            } else if((i==k & jj!=ll)|(i==ll & jj!=k)){sum_c4 <- sum_c4 +((vi+vi)^2+(vi_star+vi_star)^2)/2
            } else if((i!=k & jj==ll)|(i!=ll & jj==k)){sum_c4 <- sum_c4 +((vjj+vjj)^2+(vjj_star+vjj_star)^2)/2
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
    } else{
      whether_changepoint <- 0
      changepoint_candidate <- NA
    }
  }
  return(list(changepoint_candidate,whether_changepoint))
}

#---------------------------------------------------------------------------------------------------
#' This is the main function that runs the proposed algorithm for multiple change point detection in high dimensional data
#' @param data          a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN           a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @param test          either asymptotic or permutation test, default is the asymptotic test
#' @param npermut       number of permutations for permutation test, default is 200
#' @param siglevel      the significance level, default is 0.05
#' @param minsegment    minimum number of segments for recursive binary segmentation, default is 10
#' @return   the list of detected significant change points, including any NA's which should be removed then
#' @export

multiple_changepoint_detection <- function(data,FUN=delta0,minsegment=10,test="asymptotic",npermut=200,siglevel=0.05){
  changepoint_all <- NA
  length_data <- nrow(as.matrix(rbind(data,data)))/2
  while(length_data>minsegment){
    call_changepoint_test <- test_single_changepoint(data=data,FUN=FUN,test=test,npermut=npermut,siglevel=siglevel)
    changepoint <- call_changepoint_test[[1]]
    is_changepoint <- call_changepoint_test[[2]]
    nn_split <- nrow(data)
    if(is_changepoint==1 & changepoint>2 & changepoint<nn_split-2){
      data_before <- data[1:(changepoint-1),]
      data_after <- data[(changepoint+1):nn_split,]
      changepoint_before <- multiple_changepoint_detection(data=data_before,FUN=FUN,minsegment=minsegment,test=test,npermut=npermut,siglevel=siglevel)
      changepoint_after <- multiple_changepoint_detection(data=data_after,FUN=FUN,minsegment=minsegment,test=test,npermut=npermut,siglevel=siglevel)+changepoint
      changepoint_all <- c(changepoint,changepoint_before,changepoint_after)
      return(changepoint_all)
    } else{
      return(NA)
      break
    }
  }
  return(changepoint_all)
}

