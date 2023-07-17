You can install this R package using the following two commands in R:

library(devtools)

install_github("rezadrikvandi/HDDchangepoint")

and then load it using library(HDDchangepoint)

Details about this package can be found in the DESCRIPTION file. The main R function of the package is called "multiple_changepoint_detection" which can be applied for detecting multiple change points in high dimensional data using the method presented in the paper (there are other functions in the package to calculate other measures as detailed in the package). Also, there is a test data to try (see below for some details), as well as the real data set in the paper (see below for some details). Further details about these data sets can be found in the folder "data" in the package above.

Test data: the test data are simulated with n=40 and p=500 where there is a true change point at location 21. Below is the command to apply the R package to this test data along with the output:

multiple_changepoint_detection(data=testdata)

The output is:

$Detected change points [1] 21

$Corresponding p-values [1] 0

Real data (S&P500 index data): while the details of the real data are given in the paper, below is a simple command "with default settings" to apply the R package to this real data set along with the output (note that in the paper we use wbs which takes longer to run - wbs is also available in the package via function "multiple_changepoint_detection_wbs"):

multiple_changepoint_detection(data=SP500data)

The output of this implementation with the default settings is:

$Detected change points [1] 51 57 66 95 106 112 115

$Corresponding p-values [1] 5.637387e-09 5.064963e-04 1.266905e-05 2.495187e-07 4.083282e-03 [6] 7.150078e-05 1.281656e-02
