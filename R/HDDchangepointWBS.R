# Functions used for wild binary segmentation, written by Reza Drikvandi <reza.drikvandi@durham.ac.uk>

#---------------------------------------------------------------------------------------------------
#' This function calculates the argmax (change point candidate) and colsums of the difference distance matrix Delta for given data and dissimilarity measure
#' @param data     a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN      a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @return   the change point candidate (argmax) and colsums of the difference distance matrix Delta
#' @export

argmaxDelta <- function(data,FUN=dist1){
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
  changepoint_candidate <- which(colsumD==max(colsumD))[1]
  #changepoint_candidate <- as.numeric(which(diffdis==max(diffdis), arr.ind=TRUE)[1,2]) + 1
  maxcolsumD <- max(colsumD)
  return(c(changepoint_candidate,maxcolsumD))
}

#---------------------------------------------------------------------------------------------------
#' This function calculates the proposed test statistic T for given data and dissimilarity measure for wild binary segmentation
#' @param data     a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN      a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @param cp_estimate     change point candidate which is calculated if NULL, default is NULL
#' @return   the change point estimate together with the test statistics T and W
#' @export

test_statistic_wbs <- function(data,FUN=dist1,cp_estimate=NULL){
  nn <- nrow(data)
  d <- ncol(data)
  distance_matrix <- as.matrix(FUN(data))
  if(identical(FUN,dist))
  {
    #only for the modified Euclidean distance if used, as it requires dividing by sqrt(d)
    distance_matrix <- distance_matrix/sqrt(d)
  }
  if (is.null(cp_estimate)){
    diffdis <- matrix(0,nn,nn)
    for(i in 1:nn) {
      for (j in 2:nn) {
        diffdis[i,j] <- abs(distance_matrix[i,j]-distance_matrix[i,j-1])
      }
    }
    colsumD <- colSums(diffdis)/nn
    changepoint_estimate <- which(colsumD==max(colsumD))[1]
  } else{
    changepoint_estimate <- cp_estimate
  }
  distance_matrix <- as.matrix(FUN(data))
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
#' This function conducts the test of significance required for wild binary segmentation
#' @param data         a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN          a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @param cp_estimate     change point candidate which is calculated if NULL, default is NULL
#' @param test         either asymptotic or permutation test, default is the asymptotic test
#' @param npermut      number of permutations for permutation test, default is 200
#' @param siglevel     the significance level, default is 0.05
#' @return    the change point candidate and whether it is significant or not (1 significant, 0 not significant),
#'            as well as the p-value of the test for change point
#' @export

test_significance_changepoint <- function(data,FUN=dist1,cp_estimate=NULL,test="asymptotic",npermut=200,siglevel=0.05){
  nn <- nrow(data)
  d <- ncol(data)
  changepoint_candidate=NULL
  changepoint_estimate <- cp_estimate
  changepoint_stat <- test_statistic_wbs(data=data,FUN=FUN,cp_estimate=cp_estimate)
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
      changepoint_stat_per <- test_statistic_wbs(data=samplepermut_max,FUN=FUN,cp_estimate=cp_estimate)
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
#' This is the function that runs the proposed algorithm with wild binary segmentation for multiple change point detection in high dimensional data
#' @param data          a matrix of size nxp (i.e., n observations, each p-dimensional)
#' @param FUN           a dissimilarity measure, default is the new dissimilarity measure d(Xi,Xj)
#' @param test          either asymptotic or permutation test, default is the asymptotic test
#' @param npermut       number of permutations for permutation test, default is 200
#' @param siglevel      the significance level, default is 0.05
#' @param minsegmlength    minimum segment length for wild binary segmentation, default is 10
#' @param M             number of random draws for wild binary segmentation, default is 50
#' @return    the list of detected significant change points and the corresponding p-values
#' @export

multiple_changepoint_detection_wbs <- function(data,FUN=dist1,minsegmlength=10,M=50,test="asymptotic",npermut=200,siglevel=0.05){
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
  M <- M
  length_data <- nrow(data)
  while(length_data>minsegmlength){
    intervals <- matrix(0,M+1,2)
    intervals[1:M,] <- random.intervals(length_data,M)
    intervals[M+1,] <- c(1,length_data)
    intervals_colsums <- NULL
    for(i in 1:(M+1)){
      res_M <- argmaxDelta(data[intervals[i,1]:intervals[i,2],])
      res_M[1] <- res_M[1]+(intervals[i,1]-1)
      intervals_colsums <- rbind(res_M,intervals_colsums)
    }
    intervals_colsums <- intervals_colsums[complete.cases(intervals_colsums),]
    changepoint_estimate <- intervals_colsums[order(intervals_colsums[,2],decreasing = TRUE),][1,1]
    changepoint_estimate <- as.numeric(changepoint_estimate)
    call_changepoint_test <- test_significance_changepoint(data=data,FUN=FUN,cp_estimate=changepoint_estimate,test=test,npermut=npermut,siglevel=siglevel)
    changepoint <- call_changepoint_test[[1]]
    is_changepoint <- call_changepoint_test[[2]]
    pvalue <- call_changepoint_test[[3]]
    nn_split <- nrow(data)
    if(is_changepoint==1 & changepoint>2 & changepoint<nn_split-2){
      data_before <- data[1:(changepoint-1),]
      data_after <- data[(changepoint+1):nn_split,]
      changepoint_bef <- multiple_changepoint_detection_wbs(data=data_before,FUN=FUN,minsegmlength=minsegmlength,test=test,npermut=npermut,siglevel=siglevel)
      changepoint_before <- changepoint_bef[[1]]
      pvalue_before <- changepoint_bef[[2]]
      changepoint_aft <- multiple_changepoint_detection_wbs(data=data_after,FUN=FUN,minsegmlength=minsegmlength,test=test,npermut=npermut,siglevel=siglevel)
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

