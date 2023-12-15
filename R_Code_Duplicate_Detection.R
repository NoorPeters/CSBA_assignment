# install.packages("rjson")
# install.packages("jsonlite")
# install.packages("purrr")
# install.packages("dplyr")
# install.packages("primes")
# install.packages("vegan")
# install.packages("cluster")
library("vegan")
library("primes")
library("jsonlite")
library("rjson")
library("purrr")
library("dplyr")
library("cluster")

#LOAD DATA
json_file <-
  "insert own path"
json_data <-
  fromJSON(file = json_file)

##########################################################################################3
#CLEAN DATA

clean_data <- function(data) {
  for (i in seq_along(data)) {
    if (is.list(data[[i]])) {
      data[[i]] <- clean_data(data[[i]])
    } else if (is.character(data[[i]])) {
      #convert text to lowercase
      data[[i]] <- tolower(data[[i]])
      
      #normalize 'inch'
      data[[i]] <- gsub("(-)inch(es)?", "inch", data[[i]])
      data[[i]] <- gsub("\"", "inch", data[[i]])
      data[[i]] <- gsub(" inch(es)?", "inch", data[[i]])
      #data[[i]]<- gsub("-inch(es)?", "inch", data[[i]])
      #data[[i]]<- gsub("()(-)Inch(es)?", "inch", data[[i]])
      
      #normalize 'hz'
      data[[i]] <- gsub("(-)hertz?", "hz", data[[i]])
      data[[i]] <- gsub(" hz", "hz", data[[i]])
      data[[i]] <- gsub(" hertz", "hz", data[[i]])
    }
  }
  return(data)
}
cleaned_data <- clean_data(json_data)


#####################################################################################################
# FIND MODEL WORDS

#finding the model words from the titles and storing them in MW
find_MW_title <- function(data) {
  MW<-character(0)
  for (i in 1:length(data)) {
      title_words <- unlist(strsplit(data[[i]]$title, " "))
      #model_words <-title_words[]
      MW <- unique(c(MW, title_words))
  }
  MW <-
    MW[(regexpr(
      "[a-zA-Z0-9]*(([0-9]+[^0-9, ]+)|([^0-9, ]+[0-9]+))[a-zA-Z0-9]*", MW) > 0)]
  return(MW)
}

#adding the model words from the key-value pairs in the featuresMap and storing them in MW_2
Add_MW_value <- function(data, MW) {
  MW_values2 <- character(0)
  MW_2<-MW
  for (i in 1:length(data)) {
      for (j in 1:length(data[[i]]$featuresMap)) {
        MW_values <-
          unlist(strsplit(data[[i]][["featuresMap"]][[j]], " "))
        MW_values <-
          MW_values[(regexpr("^(\\d+(\\.\\d+)?[a-zA-Z]+$|^\\d+(\\.\\d+)?)$",MW_values) > 0)]
        MW_values <- gsub("[^0-9.]", "", MW_values)
        MW_values2 <- unique(c(MW_values2, MW_values))
      }
    }
  MW_2 <- unique(c(MW_2, MW_values2))
  MW_2 <-
    c( MW_2,c(
        "aquos",
        "bravia",
        "coby",
        "hisense",
        "lg",
        "nec",
        "panasonic",
        "philips",
        "rca",
        "samsung",
        "sanyo",
        "sharp",
        "sony",
        "tcl",
        "toshiba"
      )
    )
  MW_2 <- c(MW_2, c("hdtv", "led", "plasma", "smart", "supersonic"))
  
  return(MW_2)
}


#/////////////////////////////////////////////////////////////////////////////////////
#CREATE THE BINARY MATRIX

create_BM <- function(data, MW, MW_2){
  numProd = length(data)
  binMat <-
    matrix(0, nrow = length(MW_2), ncol = numProd)
  for (i in 1:numProd) {
      title_words_i <- unlist(strsplit(data[[i]]$title, " "))
      title_words_i <- trimws(title_words_i)
      value_words_i <- character(0)
      for (k in 1:length(data[[i]]$featuresMap)) {
        values <-
          unlist(strsplit(data[[i]][["featuresMap"]][[k]], " "))
        value_words_i <- unique(c(value_words_i, values))
      }
      value_words_i <-
        value_words_i[(regexpr(
          "^(\\d+(\\.\\d+)?[a-zA-Z]+$|^\\d+(\\.\\d+)?)$",
          value_words_i
        ) > 0)]
      value_words_i <- gsub("[^0-9.]", "", value_words_i)
      for (l in 1:length(MW)) {
        binMat[l, i] <- min(sum(grepl(MW_2[l], title_words_i, fixed = T)), 1)
        if (binMat[l, i] == 0) {
          binMat[l, i] <-
            min(sum(grepl(MW_2[l] , value_words_i, fixed = T)), 1)
        }
      }
      for (m in length(MW):length(MW_2)) {
        if (binMat[m, i] == 0) {
          binMat[m, i] <-
            min(sum(grepl(MW_2[m], value_words_i, fixed = T)), 1)#i(products)=row, m(mw)=columns
        }
      }
  }
  return(binMat)
}


#///////////////////////////////////////////////////////////////////////////////////////////////
#CREATE PERMUTATIONS FOR MINHASHING

create_perm <-function(ModelWords, numHashes){
  ogRows <- 1:length(ModelWords)
  all_primes <-
    generate_primes(min = numHashes + 1, max = numHashes ^ 2)
  perm <- matrix(data = NA,
                 nrow = length(ModelWords),
                 ncol = numHashes)
  for (i in 1:numHashes) {
    a <- sample(1:length(ModelWords), 1)
    b <- sample(1:length(ModelWords), 1)
    p <- all_primes[sample(1:length(all_primes), 1)]
    perm[, i] <- (a + b * ogRows) %% (p)
  }
  return(perm)
}

#/////////////////////////////////////////////////////////////////////////////////////////////////
#CREATE SIGNATURE MATRIX

create_sig <-function(ModelWords, numHashes, binMat){
  sigMat <- matrix(data = length(ModelWords)+1, nrow = numHashes, ncol = ncol(binMat))
  for(i in 1:length(ModelWords)){
    for(k in 1:ncol(binMat)){
      if(binMat[i,k]==1){
        sigMat[,k]<-pmin(sigMat[,k], perm[i,])
      }
    }
  }
  return(sigMat)
}

#////////////////////////////////////////////////////////////////////////////////////////
#PERFORM LSH

# Function to perform LSH
lsh <- function(matrix, bands, rows) {
  #num_hashes <- bands * rows
  candidate_pairs <- matrix(0, nrow = ncol(matrix), ncol = ncol(matrix))
  buckets <- matrix(0, nrow = bands, ncol = ncol(matrix))
  
  for (b in 1:bands) {
    chunk_b <- matrix[((bands - 1) * rows + 1):(bands * rows),]
    for(i in 1:(ncol(sigMat)-1)){
      buckets[b,i]<-paste(chunk_b[,i],collapse = "")
    }
  }
  
  for(i in 1:(ncol(matrix)-1)){ 
    for(j in (i+1):ncol(matrix)){
      for(b in 1:bands){
        if(buckets[b,i]==buckets[b,j]){
          candidate_pairs[i,j]=1
          candidate_pairs[j,i]=1
        }
      }
    }
  }
  return(candidate_pairs)
}


#////////////////////////////////////////////////////////////////////////////////////////////
#FIND REAL DUPLICATES BASED ON MODEL ID

find_realDups <- function(data){
  modelIDs_realDup<-character(0)
  nRD<-0
  for(i in 1:(length(data)-1)){
    for(j in (i+1):length(data)){
      if(data[[i]][["modelID"]]==data[[j]][["modelID"]]){
        nRD <- nRD+1
        #modelIDs_realDup[nRD]<-data[[i]][["modelID"]]
        modelIDs_realDup<-c(modelIDs_realDup, data[[i]][["modelID"]])
      }
    }
  }
  print(nRD)
  return(modelIDs_realDup)
}

#///////////////////////////////////////////////////////////////////////////////////////////
#CREATE DISTANCE MATRIX
create_Distance <- function(data, og_data, binData){
  N<-ncol(data)
  disMat <- matrix(NA, ncol = N, nrow= N)
  diag(disMat)<-0
  for(i in 1:(N-1)){
    for(j in (i+1):N){
      if ((data[i, j] == 0) |
           (og_data[[i]]$shop == og_data[[j]]$shop)) {
        disMat[i,j] = 1e+6
        disMat[j,i] = 1e+6
      }
      else{
        inter<-0
        union<-0
        for(k in 1:nrow(binData)){
          if(binData[k,i]==1&&binData[k,j]==1){
            inter <- inter+1
          }
          if(binData[k,i]==1|binData[k,j]==1){
            union<- union+1

          }
        }
        disMat[i,j]=1-inter/union
        disMat[j,i]=1-inter/union
      }
    }
  }
  return(disMat)
}

#//////////////////////////////////////////////////////////////////////////////////////////////////////
#CLUSTERING

#hierarchical clustering
calc_HC<-function(disData2, heigth){
  HC<-hclust(disData2, method = "single")
  HC_clus<- cutree(HC, h=heigth)
  
  un_HC_cluster <- unique(HC_clus)
  newClusters <- vector(mode = "list", length = length(un_HC_cluster))
  for (i in 1:length(un_HC_cluster)) {
    newClusters[[i]] <- which(HC_clus == un_HC_cluster[i])
  }
  return(newClusters)
}

#MST clustering
calc_ST <- function(disData, heigth ){
  ST<-spantree(disData, toolong = 1)
  #make sure kid does not contain any NA values
  ST$kid[is.na(ST$kid)]<-0
  ST_HC <-as.hclust(ST)
  #make sure merge does not contain any NA values
  for(i in 1:length(ST_HC$merge)){
    if(is.na(ST_HC$merge[i])){
      ST_HC$merge[i] <-0
    }
  }
  
  ST_clus <- cutree(ST_HC, h=heigth)
  un_ST_cluster <- unique(ST_clus)
  newST_clusters <- vector(mode = "list", length = length(un_ST_cluster))
  for (i in 1:length(un_ST_cluster)) {
    newST_clusters[[i]] <- which(ST_clus == un_ST_cluster[i])
  }
  return(newST_clusters)
}

#///////////////////////////////////////////////////////////////////////////////////////////////////////
#PERFORMANCE MEASURES

# Compute True Positives(duplicate when) and False Positives (FP)
calc_TPFP <-function(data, og_data){
  numTruePos <- 0
  numFalsePos <- 0
  pred <- as.matrix(which(data == 1, arr.ind = TRUE, useNames = FALSE))
  pred <- pred[(pred[,1] < pred[,2]),]
  for (i in 1:nrow(pred)) {
    if (og_data[[pred[i,1]]][["modelID"]] == og_data[[pred[i,2]]][["modelID"]]) {
      numTruePos <- numTruePos + 1
    } else {
      numFalsePos <- numFalsePos + 1
    }
  }
  return(c(numTruePos, numFalsePos, length(pred), nrow(pred)))
}

#calculate the measures after clustering
calc_CPFP_AC<-function(clusters, og_data){
  TP <-0
  FP<-0
  len_clus <- lengths(clusters)
  for(i in 1:length(clusters)){
    if(len_clus[i]>1){
      for(j in 1:(len_clus[i]-1)){
        for(k in 2:len_clus[i]){
          if(og_data[[clusters[[i]][[j]]]]$modelID == og_data[[clusters[[i]][[k]]]]$modelID){
            TP <- TP+1
          }
          else{
            FP<-FP+1
          }
        }
      }
    }
  }
  return(c(TP,FP))
}

#####################################################################################################
#RUN CODE FOR TRAINING

unlisted <- unlist(cleaned_data,recursive = F)
numProd <- length(unlisted)

MW <- find_MW_title(unlisted)#model words from Title
MW_2 <- Add_MW_value(unlisted,MW)#model words from Title and Feature Values

#Create Binary Vectors
binMat_all<-create_BM(unlisted, MW, MW_2)


seeds<-c(12,123,78,789,123789)
#number of band options = 5
resMat<-matrix(data = NA, ncol = 5*length(seeds), nrow = 18)
resMat_LSH <-matrix(NA, nrow =7 , ncol = 5*length(seeds))
for(z in 1:length(seeds)){
  set.seed(seeds[z])
  a <-sample(1:length(unlisted), length(unlisted)*0.63)
  train<-unlisted[a]
  test<-unlisted[-a]  
  
  #perform the code for train data
  binMat <- binMat_all[,a]
  #Create Permutation
  perm<-create_perm(MW_2,1000)
  #Create the signatures matrix
  sigMat <-create_sig(MW_2,1000,binMat) 
  
  #length(sigMat) = b*r must hold => (1/b)^(1/r) = t
  # higher b => more false positives
  # higher r => more false negatives
  bands<-c(50,100,200,250,500)
  rows<-c(20,10,5,4,2)
  for(t in 1:length(bands)){
    band <- bands[t]
    row <- rows[t]
    
    #perform LSH
    lshCandidateMat <- lsh(sigMat, band, row)
    
    #find the real duplicates
    modelIDs_realDup<-find_realDups(train)
    un_MID <- unique(modelIDs_realDup)
    nRealDups<-length(modelIDs_realDup)
    
    #create the distance matrix
    disMat <- create_Distance(lshCandidateMat, train, binMat)#input for spantree
    disMat2 <- as.dist(disMat)#input for hclust
    
    #clustering with hclust(HC) and spantree(ST), try different heigths
    HC_clusters3<-calc_HC(disMat2, 0.3)
    HC_clusters4<-calc_HC(disMat2, 0.4) 
    HC_clusters5<-calc_HC(disMat2, 0.5) 
    ST_clusters3<-calc_ST(disMat,0.3)
    ST_clusters4<-calc_ST(disMat,0.4)
    ST_clusters5<-calc_ST(disMat,0.5)
    
    # Performance measures LSH
    result_TPFP <-calc_TPFP(lshCandidateMat, train)
    numTP <- result_TPFP[1]
    numFP <- result_TPFP[2]
    numP <- result_TPFP[3]
    rowP <- result_TPFP[4]
    
    #rowP = number of comparisons made
    fraction <- rowP/((length(train)*(length(train)-1))/2)
    PQ<- numTP / rowP
    PC <- numTP / nRealDups
    Fstar <- (PQ * PC * 2) / (PQ + PC)
    
    
    resMat_LSH[1,(5*(z-1))+t] <- row
    resMat_LSH[2,(5*(z-1))+t] <- band
    resMat_LSH[3,(5*(z-1))+t] <- (1/band)^(1/row)
    resMat_LSH[4,(5*(z-1))+t] <- fraction
    resMat_LSH[5,(5*(z-1))+t] <- PC
    resMat_LSH[6,(5*(z-1))+t] <- PQ
    resMat_LSH[7,(5*(z-1))+t] <- Fstar
    
    #performance measures hclust(HC) and spantree(ST)
    #height = 0.3
    result_TPFP_HC3 <- calc_CPFP_AC(HC_clusters3, train)
    TP_HC3 <- result_TPFP_HC3[1]
    FP_HC3 <- result_TPFP_HC3[2]
    precision_HC3 <- TP_HC3/(FP_HC3+TP_HC3)
    recall_HC3 <- TP_HC3/nRealDups
    F1_HC3<- (2*precision_HC3*recall_HC3)/(precision_HC3+recall_HC3)
    
    #height = 0.4
    result_TPFP_HC4 <- calc_CPFP_AC(HC_clusters4, train)
    TP_HC4 <- result_TPFP_HC4[1]
    FP_HC4 <- result_TPFP_HC4[2]
    precision_HC4 <- TP_HC4/(FP_HC4+TP_HC4)
    recall_HC4 <- TP_HC4/nRealDups
    F1_HC4<- (2*precision_HC4*recall_HC4)/(precision_HC4+recall_HC4)
    
    #height = 0.5
    result_TPFP_HC5 <- calc_CPFP_AC(HC_clusters5, train)
    TP_HC5 <- result_TPFP_HC5[1]
    FP_HC5 <- result_TPFP_HC5[2]
    precision_HC5 <- TP_HC5/(FP_HC5+TP_HC5)
    recall_HC5 <- TP_HC5/nRealDups
    F1_HC5<- (2*precision_HC5*recall_HC5)/(precision_HC5+recall_HC5)
    
    #height = 0.3
    result_TPFP_ST3 <- calc_CPFP_AC(ST_clusters3, train)
    TP_ST3 <- result_TPFP_ST3[1]
    FP_ST3 <- result_TPFP_ST3[2]
    precision_ST3 <- TP_ST3/(FP_ST3+TP_ST3)
    recall_ST3 <- TP_ST3/nRealDups
    F1_ST3<- (2*precision_ST3*recall_ST3)/(precision_ST3+recall_ST3)
    
    #height = 0.4
    result_TPFP_ST4 <- calc_CPFP_AC(ST_clusters4, train)
    TP_ST4 <- result_TPFP_ST4[1]
    FP_ST4 <- result_TPFP_ST4[2]
    precision_ST4 <- TP_ST4/(FP_ST4+TP_ST4)
    recall_ST4 <- TP_ST4/nRealDups
    F1_ST4<- (2*precision_ST4*recall_ST4)/(precision_ST4+recall_ST4)
    
    #height = 0.5
    result_TPFP_ST5 <- calc_CPFP_AC(ST_clusters5, train)
    TP_ST5 <- result_TPFP_ST5[1]
    FP_ST5 <- result_TPFP_ST5[2]
    precision_ST5 <- TP_ST5/(FP_ST5+TP_ST5)
    recall_ST5 <- TP_ST5/nRealDups
    F1_ST5<- (2*precision_ST5*recall_ST5)/(precision_ST5+recall_ST5)
    
    #save results in matrix
    resMat[1,(5*(z-1))+t]<-precision_HC3
    resMat[2,(5*(z-1))+t]<-recall_HC3
    resMat[3,(5*(z-1))+t]<-F1_HC3
    resMat[4,(5*(z-1))+t]<-precision_HC4
    resMat[5,(5*(z-1))+t]<-recall_HC4
    resMat[6,(5*(z-1))+t]<-F1_HC4
    resMat[7,(5*(z-1))+t]<-precision_HC5
    resMat[8,(5*(z-1))+t]<-recall_HC5
    resMat[9,(5*(z-1))+t]<-F1_HC5
    resMat[10,(5*(z-1))+t]<-precision_ST3
    resMat[11,(5*(z-1))+t]<-recall_ST3
    resMat[12,(5*(z-1))+t]<-F1_ST3
    resMat[13,(5*(z-1))+t]<-precision_ST4
    resMat[14,(5*(z-1))+t]<-recall_ST4
    resMat[15,(5*(z-1))+t]<-F1_ST4
    resMat[16,(5*(z-1))+t]<-precision_ST5
    resMat[17,(5*(z-1))+t]<-recall_ST5
    resMat[18,(5*(z-1))+t]<-F1_ST5
    
  }
  
}
#prepare data for plotting
resMat[is.na(resMat)]<-0
resMat_LSH[is.na(resMat_LSH)]<-0
resMat_avg<-matrix(data=0, nrow=18, ncol=5)
resMat_avg[,1]<-rowMeans(resMat[,c(1,6,11,16,21)])
resMat_avg[,2]<-rowMeans(resMat[,c(2,7,12,17,22)])
resMat_avg[,3]<-rowMeans(resMat[,c(3,8,13,18,23)])
resMat_avg[,4]<-rowMeans(resMat[,c(4,9,14,19,24)])
resMat_avg[,5]<-rowMeans(resMat[,c(5,10,15,20,25)])

resMat_LSH_avg <- matrix(data=0, nrow = 7, ncol = 5)
resMat_LSH_avg[,1]<-rowMeans(resMat_LSH[,c(1,6,11,16,21)])
resMat_LSH_avg[,2]<-rowMeans(resMat_LSH[,c(2,7,12,17,22)])
resMat_LSH_avg[,3]<-rowMeans(resMat_LSH[,c(3,8,13,18,23)])
resMat_LSH_avg[,4]<-rowMeans(resMat_LSH[,c(4,9,14,19,24)])
resMat_LSH_avg[,5]<-rowMeans(resMat_LSH[,c(5,10,15,20,25)])

plot_mat <- matrix(data=0, nrow = 22, ncol = 5)
plot_mat[1:18,]<-resMat_avg
plot_mat[19,]<-resMat_LSH_avg[4,]#add ratio
plot_mat[20,]<-resMat_LSH_avg[7,]#add fstar
plot_mat[21,]<-resMat_LSH_avg[5,]#add PC
plot_mat[22,]<-resMat_LSH_avg[6,]#add PQ

#training plots
# Plot the chart for HC f1
plot(y = plot_mat[9,],x = plot_mat[19,], type = "o", col = "red",
     xlab = "Fraction of Comparisons", ylab = "F1 ",
     main = "F1 over Fraction of Comparisons for HC")
lines(y=plot_mat[c(6),],x = plot_mat[19,], type = "o", col = "blue")
lines(y=plot_mat[c(3),],x = plot_mat[19,], type = "o", col = "green")
legend("topright", legend = c("Heigth 0.5", "Heigth 0.4", "Heigth 0.3"), col = c("red", "blue","green"), lty = 1, cex = 0.8)

#Plot the chart for ST f1
plot(y = plot_mat[18,],x = plot_mat[19,], type = "o", col = "red",
     xlab = "Fraction of Comparisons", ylab = "F1 ",
     main = "F1 over Fraction of Comparisons for ST")
lines(y=plot_mat[c(15),],x = plot_mat[19,], type = "o", col = "blue")
lines(y=plot_mat[c(12),],x = plot_mat[19,], type = "o", col = "green")
legend("topright", legend = c("Heigth 0.5", "Heigth 0.4", "Heigth 0.3"), col = c("red", "blue","green"), lty = 1, cex = 0.8)

#plot F1star
plot(y = plot_mat[20,],x = plot_mat[19,], type = "o", col = "purple",
     xlab = "Fraction of Comparisons", ylab = "F1star ",
     main = "F1star over Fraction of Comparisons")

#plot PC
plot(y = plot_mat[21,],x = plot_mat[19,], type = "o", col = "darkorange",
     xlab = "Fraction of Comparisons", ylab = "Pair Completeness ",
     main = "Pair Completeness over Fraction of Comparisons")

#plot PQ
plot(y = plot_mat[22,],x = plot_mat[19,], type = "o", col = "maroon2",
     xlab = "Fraction of Comparisons", ylab = "Pair Quality ",
     main = "Pair Quality over Fraction of Comparisons")



#####################################################################################################
#RUN CODE FOR TESTING

seeds<-c(12,123,78,789,123789)
#number of band options = 5
resMat_test<-matrix(data = NA, ncol = 5*length(seeds), nrow = 13)
for(z in 1:length(seeds)){
  set.seed(seeds[z])
  a <-sample(1:length(unlisted), length(unlisted)*0.63)
  train<-unlisted[a]
  test<-unlisted[-a]  
  
  #perform the code for train data
  binMat <- binMat_all[,-a]
  #Create Permutation
  perm<-create_perm(MW_2,1000)
  #Create the signatures matrix
  sigMat <-create_sig(MW_2,1000,binMat) 
  
  #length(sigMat) = b*r must hold => (1/b)^(1/r) = t
  # higher b => more false positives
  # higher r => more false negatives
  bands<-c(50,100,200,250,500)
  rows<-c(20,10,5,4,2)
  for(t in 1:length(bands)){
    band <- bands[t]
    row <- rows[t]
    
    #perform LSH
    lshCandidateMat <- lsh(sigMat, band, row)
    
    #find the real duplicates
    modelIDs_realDup<-find_realDups(test)
    un_MID <- unique(modelIDs_realDup)
    nRealDups<-length(modelIDs_realDup)
    
    #create the distance matrix
    disMat <- create_Distance(lshCandidateMat, test, binMat)#input for spantree
    disMat2 <- as.dist(disMat)#input for hclust
    
    #clustering with hclust(HC) and spantree(ST), try different heigths
    HC_clusters5<-calc_HC(disMat2, 0.5) 
    ST_clusters5<-calc_ST(disMat,0.5)
    
    # Performance measures LSH
    result_TPFP <-calc_TPFP(lshCandidateMat, test)
    numTP <- result_TPFP[1]
    numFP <- result_TPFP[2]
    numP <- result_TPFP[3]
    rowP <- result_TPFP[4]
    
    #rowP = number of comparisons made
    fraction <- rowP/((length(test)*(length(test)-1))/2)
    PQ<- numTP / rowP
    PC <- numTP / nRealDups
    Fstar <- (PQ * PC * 2) / (PQ + PC)
    
    
    resMat_test[1,(5*(z-1))+t] <- row
    resMat_test[2,(5*(z-1))+t] <- band
    resMat_test[3,(5*(z-1))+t] <- (1/band)^(1/row)
    resMat_test[4,(5*(z-1))+t] <- fraction
    resMat_test[5,(5*(z-1))+t] <- PC
    resMat_test[6,(5*(z-1))+t] <- PQ
    resMat_test[7,(5*(z-1))+t] <- Fstar
    
    #performance measures hclust(HC) and spantree(ST)
    #height = 0.5
    result_TPFP_HC5 <- calc_CPFP_AC(HC_clusters5, test)
    TP_HC5 <- result_TPFP_HC5[1]
    FP_HC5 <- result_TPFP_HC5[2]
    precision_HC5 <- TP_HC5/(FP_HC5+TP_HC5)
    recall_HC5 <- TP_HC5/nRealDups
    F1_HC5<- (2*precision_HC5*recall_HC5)/(precision_HC5+recall_HC5)
    
    #height = 0.5
    result_TPFP_ST5 <- calc_CPFP_AC(ST_clusters5, test)
    TP_ST5 <- result_TPFP_ST5[1]
    FP_ST5 <- result_TPFP_ST5[2]
    precision_ST5 <- TP_ST5/(FP_ST5+TP_ST5)
    recall_ST5 <- TP_ST5/nRealDups
    F1_ST5<- (2*precision_ST5*recall_ST5)/(precision_ST5+recall_ST5)
    
    #store results
    resMat_test[8,(5*(z-1))+t]<-precision_HC5
    resMat_test[9,(5*(z-1))+t]<-recall_HC5
    resMat_test[10,(5*(z-1))+t]<-F1_HC5
    resMat_test[11,(5*(z-1))+t]<-precision_ST5
    resMat_test[12,(5*(z-1))+t]<-recall_ST5
    resMat_test[13,(5*(z-1))+t]<-F1_ST5
    
  }
  
}
#prepare data for plotting
plot_mat_test <- matrix(data=0, nrow = 13, ncol = 5)
plot_mat_test[,1]<-rowMeans(resMat_test[,c(1,6,11,16,21)])
plot_mat_test[,2]<-rowMeans(resMat_test[,c(2,7,12,17,22)])
plot_mat_test[,3]<-rowMeans(resMat_test[,c(3,8,13,18,23)])
plot_mat_test[,4]<-rowMeans(resMat_test[,c(4,9,14,19,24)])
plot_mat_test[,5]<-rowMeans(resMat_test[,c(5,10,15,20,25)])

# Plot the chart for F1
plot(y = plot_mat_test[10,],x = plot_mat_test[4,], type = "o", col = "red",
     xlab = "Fraction of Comparisons", ylab = "F1 ",
     main = "TEST: F1 over Fraction of Comparisons for HC and ST")
lines(y=plot_mat_test[13,],x = plot_mat_test[4,], type = "o", col = "blue")
legend("topright", legend = c("HC", "ST"), col = c("red", "blue"), lty = 1, cex = 1)


#Plot the chart for F1star
plot(y = plot_mat_test[7,],x = plot_mat_test[4,], type = "o", col = "purple",
     xlab = "Fraction of Comparisons", ylab = "F1 ",
     main = "TEST: F1star over Fraction of Comparisons")

#plot PC
plot(y = plot_mat_test[5,],x = plot_mat_test[4,], type = "o", col = "darkorange",
     xlab = "Fraction of Comparisons", ylab = "Pair Completeness ",
     main = "TEST: Pair Completeness over Fraction of Comparisons")

#plot PQ
plot(y = plot_mat_test[6,],x = plot_mat_test[4,], type = "o", col = "maroon2",
     xlab = "Fraction of Comparisons", ylab = "Pair Quality ",
     main = "TEST: Pair Quality over Fraction of Comparisons")
