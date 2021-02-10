//
//  main.cpp
//
//  Created and written by Jesse Kreger (kregerj@uci.edu)
//  Compiled and ran using Xcode version 12 on a Mac
//  Copyright © 2021 Jesse Kreger
//
//  This code runs simulations using a hybrid stochastic-deterministic algorithm to explore multiple infection and evolution in HIV. We assume k = 1 (so there is a wild-type and mutant strain), and S = 3 (so a maximum of 3 viral copies are transferred per synaptic infection event). Note that there are multiple variables and functions defined before the main routine of the program.
//
//

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <iostream>
#include <random>
#include <math.h>
#include <string>

using namespace std;
double q = 9; //parameter for total number of cells
double lambda = 3.1 * pow(10,7) * 8 * 0.45 / 7; //parameter for generation of uninfected cells
double beta = (8 * 0.45 / pow(10,q)) * 1; //parameter for rate of free virus transmission
double gammaa = (8 * 0.45 / pow(10,q)) * 0; //parameter for rate of synaptic transmission
double d = lambda / pow(10,q); //parameter for uninfected cell death rate
double cda = 0.45; //parameter for infected cell death rate
const int SS = 3; //parameter for number of viruses transferred per synaptic infection event
//note that based on complier you might need to use #define SS 3 or something similar
double mu = 0.00003; //parameter for mutation rate
const int N = 12; //parameter for maximum infection multiplicity + 1
//note that based on complier you might need to use #define N 12 or something similar
double h = 0.00001; //parameter for numerical solution step size
double M = 50; //parameter for hybrid algorithm size threshold
double sizestop = 5 * pow(10,8); //parameter for infected cell population simulation stopping size
int numberofloops = 3; //parameter for number of simulations to run
const int G = 3958; //parameter for number of stochastic Gillespie events
double fitness_ab = 1; //parameter for fitness of wild-type
double fitness_Ab = 1; //parameter for fitness of mutant
std::string filename = "filename.csv"; //file to save data

//initialize parameters and setup simulation
double y[N][N];
double x[N][N];
int popsize[N][N];
double logr[G];
double integral[G];
double wold[G];
double wnew[G];
double reactsize[G];
int doreact[G];
double timecalcold[G];
double timecalcnew[G];
double tau[G];
double mu0 = (1-mu);
double mu1 = mu;
double t = 0;
double told = 0;
double htemp = 0;
double save = 0;
double stop;
double minn;
int count_ab;
int count_Ab;
int tracker;
int i;
int i_ab;
int i_Ab;
int j;
double jj;
double SSS = SS;
double ii_ab;
double ii_Ab;
double infected;
double bigZ;
double bigH;
double bigH2;
double bigH1;
double meanf_ab;
double meanf_Ab;
double actualinfected_ab;
double actualinfected_Ab;
double nov_ab;
double nov_Ab;
double multN;
double averagemultiplicty = 0;
double full;
double fullS;
double full2;
double full1;
double randomprob;
int calclocation;
int loops;
double ww = 0;
double mm = 0;
double p3 = 0;
double print = 0;
double coinfected = 0;

double ptf_fv_ab; //free virus transmission events
double ptf_fv_Ab;

double ptf_st_0; //synaptic transmission transmission events
double ptf_st_1;
double ptf_st_2;
double ptf_st_3;
double ptf_st_4;
double ptf_st_5;
double ptf_st_6;
double ptf_st_7;
double ptf_st_8;
double ptf_st_9;
double syncotranspick[10];
double syncotrans[10];

//functions (these functions are used in the program and are declared before the main routine)
//this function calculates the number of cells in each relevant subpopulation
double calculatesubpopulations() {
    infected = 0;
    bigZ = 0;
    bigH = 0;
    bigH2 = 0;
    bigH1 = 0;
    meanf_ab = 0;
    meanf_Ab = 0;
    coinfected = 0;
    actualinfected_Ab = 0;
    
    for (j=0; j<10; j++) {
        syncotranspick[j] = 0;
        syncotrans[j] = 0;
    }
    for (i_ab=0; i_ab<N; i_ab++) {
        for (i_Ab=0; i_Ab<N; i_Ab++) {
            if (i_ab>0 || i_Ab>0) {
                if ((i_ab+i_Ab) < N) {
                    ii_ab = i_ab;
                    ii_Ab = i_Ab;
                    ww = (ii_ab/(ii_ab+ii_Ab)) * fitness_ab;
                    mm = (ii_Ab/(ii_ab+ii_Ab)) * fitness_Ab;
                    p3 = (ii_ab/(ii_ab+ii_Ab)) * (1-fitness_ab) + (ii_Ab/(ii_ab+ii_Ab)) * (1-fitness_Ab);
                    if (i_ab > 0 && i_Ab > 0) {
                        //uncomment the following two lines to turn complementation/interference on
                        //mm = (ii_Ab/(ii_ab+ii_Ab)) * fitness_ab;
                        //p3 = (1-fitness_ab);
                        coinfected = coinfected + y[i_ab][i_Ab];
                    }
                    infected = infected + y[i_ab][i_Ab];
                    meanf_ab = meanf_ab + ww * y[i_ab][i_Ab];
                    meanf_Ab = meanf_Ab + mm * y[i_ab][i_Ab];
                    for (j=0; j<4; j++) {
                        jj = j;
                        syncotranspick[j] = syncotranspick[j] + (pow((ww),jj) * pow((mm),SSS-jj)) * y[i_ab][i_Ab];
                    }
                    syncotranspick[4] = syncotranspick[4] + (pow((ww),2) * pow((mm),0) * pow((p3),1)) * y[i_ab][i_Ab];
                    syncotranspick[5] = syncotranspick[5] + (pow((ww),1) * pow((mm),1) * pow((p3),1)) * y[i_ab][i_Ab];
                    syncotranspick[6] = syncotranspick[6] + (pow((ww),0) * pow((mm),2) * pow((p3),1)) * y[i_ab][i_Ab];
                    syncotranspick[7] = syncotranspick[7] + (pow((ww),1) * pow((mm),0) * pow((p3),2)) * y[i_ab][i_Ab];
                    syncotranspick[8] = syncotranspick[8] + (pow((ww),0) * pow((mm),1) * pow((p3),2)) * y[i_ab][i_Ab];
                    syncotranspick[9] = syncotranspick[9] + (pow((ww ),0) * pow((mm),0) * pow((p3),3)) * y[i_ab][i_Ab];
                }
                if (i_Ab > 0) {
                    actualinfected_Ab = actualinfected_Ab + y[i_ab][i_Ab];
                }
            }
        }
    }
    bigZ = meanf_ab + meanf_Ab;
    syncotranspick[0] = syncotranspick[0] * 6 / 1 / 6;
    syncotranspick[1] = syncotranspick[1] * 6 / 1 / 2;
    syncotranspick[2] = syncotranspick[2] * 6 / 2 / 1;
    syncotranspick[3] = syncotranspick[3] * 6 / 6 / 1;
    syncotranspick[4] = syncotranspick[4] * 6 / 2 / 1 / 1;
    syncotranspick[5] = syncotranspick[5] * 6 / 1 / 1 / 1;
    syncotranspick[6] = syncotranspick[6] * 6 / 1 / 2 / 1;
    syncotranspick[7] = syncotranspick[7] * 6 / 1 / 1 / 2;
    syncotranspick[8] = syncotranspick[8] * 6 / 1 / 1 / 2;
    syncotranspick[9] = syncotranspick[9] * 6 / 1 / 1 / 6;
    
    syncotrans[0] = pow(mu0,3)*pow(mu1,0)*syncotranspick[0] + pow(mu0,2)*pow(mu1,1)*syncotranspick[1] + pow(mu0,1)*pow(mu1,2)*syncotranspick[2] + pow(mu0,0)*pow(mu1,3)*syncotranspick[3];
    syncotrans[1] = pow(mu0,3)*pow(mu1,0)*syncotranspick[1] + 2*pow(mu0,1)*pow(mu1,2)*syncotranspick[1] + 3*pow(mu0,2)*pow(mu1,1)*syncotranspick[0] + 2*pow(mu0,2)*pow(mu1,1)*syncotranspick[2] + pow(mu0,0)*pow(mu1,3)*syncotranspick[2] + 3*pow(mu0,1)*pow(mu1,2)*syncotranspick[3];
    syncotrans[2] = pow(mu0,3)*pow(mu1,0)*syncotranspick[2] + 2*pow(mu0,1)*pow(mu1,2)*syncotranspick[2] + 3*pow(mu0,2)*pow(mu1,1)*syncotranspick[3] + 2*pow(mu0,2)*pow(mu1,1)*syncotranspick[1] + pow(mu0,0)*pow(mu1,3)*syncotranspick[1] + 3*pow(mu0,1)*pow(mu1,2)*syncotranspick[0];
    syncotrans[3] = pow(mu0,3)*pow(mu1,0)*syncotranspick[3] + pow(mu0,2)*pow(mu1,1)*syncotranspick[2] + pow(mu0,1)*pow(mu1,2)*syncotranspick[1] + pow(mu0,0)*pow(mu1,3)*syncotranspick[0];
    syncotrans[4] = pow(mu0,2)*pow(mu1,0)*syncotranspick[4] + pow(mu0,1)*pow(mu1,1)*syncotranspick[5] + pow(mu0,0)*pow(mu1,2)*syncotranspick[6];
    syncotrans[5] = 2*pow(mu0,1)*pow(mu1,1)*syncotranspick[4] + pow(mu0,2)*pow(mu1,0)*syncotranspick[5] + pow(mu0,0)*pow(mu1,2)*syncotranspick[5] + 2*pow(mu0,1)*pow(mu1,1)*syncotranspick[6];
    syncotrans[6] = pow(mu0,2)*pow(mu1,0)*syncotranspick[6] + pow(mu0,1)*pow(mu1,1)*syncotranspick[5] + pow(mu0,0)*pow(mu1,2)*syncotranspick[4];
    syncotrans[7] = pow(mu0,1)*pow(mu1,0)*syncotranspick[7] + pow(mu0,0)*pow(mu1,1)*syncotranspick[8];
    syncotrans[8] = pow(mu0,1)*pow(mu1,0)*syncotranspick[8] + pow(mu0,0)*pow(mu1,1)*syncotranspick[7];

    bigH = syncotrans[0] + syncotrans[1] + syncotrans[2] + syncotrans[3];
    bigH2 = syncotrans[4] + syncotrans[5] + syncotrans[6];
    bigH1 = syncotrans[7] + syncotrans[8];

    return (infected,bigZ,bigH,bigH2,bigH1,meanf_ab,meanf_Ab);
}

//this function calculates the number of cells in each relevant subpopulation to print to the file
double calculatesubpopulationstoprint() {
    infected = 0;
    bigZ = 0;
    bigH = 0;
    bigH2 = 0;
    bigH1 = 0;
    meanf_ab = 0;
    meanf_Ab = 0;
    actualinfected_ab = 0;
    actualinfected_Ab = 0;
    nov_ab = 0;
    nov_Ab = 0;
    coinfected = 0;
    
    for (j=0; j<10; j++) {
        syncotranspick[j] = 0;
        syncotrans[j] = 0;
    }
    averagemultiplicty = 0;
    for (i_ab=0; i_ab<N; i_ab++) {
        for (i_Ab=0; i_Ab<N; i_Ab++) {
            if (i_ab>0 || i_Ab>0) {
                if ((i_ab+i_Ab) < N) {
                    ii_ab = i_ab;
                    ii_Ab = i_Ab;
                    ww = (ii_ab/(ii_ab+ii_Ab)) * fitness_ab;
                    mm = (ii_Ab/(ii_ab+ii_Ab)) * fitness_Ab;
                    p3 = (ii_ab/(ii_ab+ii_Ab)) * (1-fitness_ab) + (ii_Ab/(ii_ab+ii_Ab)) * (1-fitness_Ab);
                    if (i_ab > 0 && i_Ab > 0) {
                        //uncomment the following two lines to turn complementation/interference on
                        //mm = (ii_Ab/(ii_ab+ii_Ab)) * fitness_ab;
                        //p3 = (1-fitness_ab);
                        coinfected = coinfected + y[i_ab][i_Ab];
                    }
                    infected = infected + y[i_ab][i_Ab];
                    meanf_ab = meanf_ab + ww * y[i_ab][i_Ab];
                    meanf_Ab = meanf_Ab + mm * y[i_ab][i_Ab];
                    for (j=0; j<4; j++) {
                        jj = j;
                        syncotranspick[j] = syncotranspick[j] + (pow((ww),jj) * pow((mm),SSS-jj)) * y[i_ab][i_Ab];
                    }
                    syncotranspick[4] = syncotranspick[4] + (pow((ww),2) * pow((mm),0) * pow((p3),1)) * y[i_ab][i_Ab];
                    syncotranspick[5] = syncotranspick[5] + (pow((ww),1) * pow((mm),1) * pow((p3),1)) * y[i_ab][i_Ab];
                    syncotranspick[6] = syncotranspick[6] + (pow((ww),0) * pow((mm),2) * pow((p3),1)) * y[i_ab][i_Ab];
                    syncotranspick[7] = syncotranspick[7] + (pow((ww),1) * pow((mm),0) * pow((p3),2)) * y[i_ab][i_Ab];
                    syncotranspick[8] = syncotranspick[8] + (pow((ww),0) * pow((mm),1) * pow((p3),2)) * y[i_ab][i_Ab];
                    syncotranspick[9] = syncotranspick[9] + (pow((ww ),0) * pow((mm),0) * pow((p3),3)) * y[i_ab][i_Ab];
                    averagemultiplicty = averagemultiplicty + (i_ab+i_Ab)*y[i_ab][i_Ab];
                }
                if (i_ab > 0) {
                    actualinfected_ab = actualinfected_ab + y[i_ab][i_Ab];
                    nov_ab = nov_ab + ii_ab*y[i_ab][i_Ab];
                }
                if (i_Ab > 0) {
                    actualinfected_Ab = actualinfected_Ab + y[i_ab][i_Ab];
                    nov_Ab = nov_Ab + ii_Ab*y[i_ab][i_Ab];
                }
            }
        }
    }

    averagemultiplicty = averagemultiplicty / infected;
    bigZ = meanf_ab + meanf_Ab;
    syncotrans[0] = syncotrans[0] * 6 / 1 / 6;
    syncotrans[1] = syncotrans[1] * 6 / 1 / 2;
    syncotrans[2] = syncotrans[2] * 6 / 2 / 1;
    syncotrans[3] = syncotrans[3] * 6 / 6 / 1;
    syncotrans[4] = syncotrans[4] * 6 / 2 / 1 / 1;
    syncotrans[5] = syncotrans[5] * 6 / 1 / 1 / 1;
    syncotrans[6] = syncotrans[6] * 6 / 1 / 2 / 1;
    syncotrans[7] = syncotrans[7] * 6 / 1 / 1 / 2;
    syncotrans[8] = syncotrans[8] * 6 / 1 / 1 / 2;
    syncotrans[9] = syncotrans[9] * 6 / 1 / 1 / 6;
    
    syncotrans[0] = pow(mu0,3)*pow(mu1,0)*syncotranspick[0] + pow(mu0,2)*pow(mu1,1)*syncotranspick[1] + pow(mu0,1)*pow(mu1,2)*syncotranspick[2] + pow(mu0,0)*pow(mu1,3)*syncotranspick[3];
    syncotrans[1] = pow(mu0,3)*pow(mu1,0)*syncotranspick[1] + 2*pow(mu0,1)*pow(mu1,2)*syncotranspick[1] + 3*pow(mu0,2)*pow(mu1,1)*syncotranspick[0] + 2*pow(mu0,2)*pow(mu1,1)*syncotranspick[2] + pow(mu0,0)*pow(mu1,3)*syncotranspick[2] + 3*pow(mu0,1)*pow(mu1,2)*syncotranspick[3];
    syncotrans[2] = pow(mu0,3)*pow(mu1,0)*syncotranspick[2] + 2*pow(mu0,1)*pow(mu1,2)*syncotranspick[2] + 3*pow(mu0,2)*pow(mu1,1)*syncotranspick[3] + 2*pow(mu0,2)*pow(mu1,1)*syncotranspick[1] + pow(mu0,0)*pow(mu1,3)*syncotranspick[1] + 3*pow(mu0,1)*pow(mu1,2)*syncotranspick[0];
    syncotrans[3] = pow(mu0,3)*pow(mu1,0)*syncotranspick[3] + pow(mu0,2)*pow(mu1,1)*syncotranspick[2] + pow(mu0,1)*pow(mu1,2)*syncotranspick[1] + pow(mu0,0)*pow(mu1,3)*syncotranspick[0];
    syncotrans[4] = pow(mu0,2)*pow(mu1,0)*syncotranspick[4] + pow(mu0,1)*pow(mu1,1)*syncotranspick[5] + pow(mu0,0)*pow(mu1,2)*syncotranspick[6];
    syncotrans[5] = 2*pow(mu0,1)*pow(mu1,1)*syncotranspick[4] + pow(mu0,2)*pow(mu1,0)*syncotranspick[5] + pow(mu0,0)*pow(mu1,2)*syncotranspick[5] + 2*pow(mu0,1)*pow(mu1,1)*syncotranspick[6];
    syncotrans[6] = pow(mu0,2)*pow(mu1,0)*syncotranspick[6] + pow(mu0,1)*pow(mu1,1)*syncotranspick[5] + pow(mu0,0)*pow(mu1,2)*syncotranspick[4];
    syncotrans[7] = pow(mu0,1)*pow(mu1,0)*syncotranspick[7] + pow(mu0,0)*pow(mu1,1)*syncotranspick[8];
    syncotrans[8] = pow(mu0,1)*pow(mu1,0)*syncotranspick[8] + pow(mu0,0)*pow(mu1,1)*syncotranspick[7];
    bigH = syncotrans[0] + syncotrans[1] + syncotrans[2] + syncotrans[3];
    bigH2 = syncotrans[4] + syncotrans[5] + syncotrans[6];
    bigH1 = syncotrans[7] + syncotrans[8];
    return (infected,bigZ,bigH,bigH2,bigH1,meanf_ab,meanf_Ab,actualinfected_ab,actualinfected_Ab,nov_ab,nov_Ab);
}

//this function makes one numerical step in the ODE system
double numericalstep(double numericalstep) {
    for (i_ab=0; i_ab<N; i_ab++) {
        for (i_Ab=0; i_Ab<N; i_Ab++) {
            if ((i_ab+i_Ab) <= N-1) {
                if (popsize[i_ab][i_Ab] == 1) {
                    full = 1;
                    ptf_fv_ab = 0;
                    ptf_fv_Ab = 0;
                    fullS = 1;
                    full2 = 1;
                    full1 = 1;
                    ptf_st_0 = 0;
                    ptf_st_1 = 0;
                    ptf_st_2 = 0;
                    ptf_st_3 = 0;
                    ptf_st_4 = 0;
                    ptf_st_5 = 0;
                    ptf_st_6 = 0;
                    ptf_st_7 = 0;
                    ptf_st_8 = 0;
                    ptf_st_9 = 0;

                    if ((i_ab+i_Ab) == N-1) {
                        full = 0;
                    }
                    if ((i_ab+i_Ab) > N-1-SS) {
                        fullS = 0;
                    }
                    if ((i_ab+i_Ab) > N-1-SS+1) {
                        full2 = 0;
                    }
                    if ((i_ab+i_Ab) > N-1-SS+2) {
                        full1 = 0;
                    }
                    
                    if (i_ab > 0) {
                        ptf_fv_ab = beta*(mu0*meanf_ab + mu1*meanf_Ab)*x[i_ab-1][i_Ab];
                    }
                    if (i_Ab > 0) {
                        ptf_fv_Ab = beta*(mu1*meanf_ab + mu0*meanf_Ab)*x[i_ab][i_Ab-1];
                    }
                    
                    if ((i_ab > -1) && (i_Ab-SS) > -1) {
                        ptf_st_0 = gammaa*(syncotrans[0])*x[i_ab][i_Ab-SS];
                    }
                    if ((i_ab-1) > -1 && (i_Ab-SS+1) > -1) {
                        ptf_st_1 = gammaa*(syncotrans[1])*x[i_ab-1][i_Ab-SS+1];
                    }
                    if ((i_ab-2) > -1 && (i_Ab-SS+2) > -1) {
                        ptf_st_2 = gammaa*(syncotrans[2])*x[i_ab-2][i_Ab-SS+2];
                    }
                    if ((i_ab-3) > -1 && (i_Ab-SS+3) > -1) {
                        ptf_st_3 = gammaa*(syncotrans[3])*x[i_ab-3][i_Ab-SS+3];
                    }
                    
                    if ((i_ab-2) > -1 && (i_Ab) > -1) {
                        ptf_st_4 = gammaa*(syncotrans[4])*x[i_ab-2][i_Ab];
                    }
                    if ((i_ab-1) > -1 && (i_Ab-1) > -1) {
                        ptf_st_5 = gammaa*(syncotrans[5])*x[i_ab-1][i_Ab-1];
                    }
                    if ((i_ab) > -1 && (i_Ab-2) > -1) {
                        ptf_st_6 = gammaa*(syncotrans[6])*x[i_ab][i_Ab-2];
                    }
                    
                    if ((i_ab-1) > -1 && (i_Ab) > -1) {
                        ptf_st_7 = gammaa*(syncotrans[7])*x[i_ab-1][i_Ab];
                    }
                    if ((i_ab) > -1 && (i_Ab-1) > -1) {
                        ptf_st_8 = gammaa*(syncotrans[8])*x[i_ab][i_Ab-1];
                    }
                 
                    if (i_ab == 0 && i_Ab == 0) {
                        y[0][0] = x[0][0]+numericalstep*(lambda-beta*bigZ*x[0][0]-gammaa*(bigH+bigH2+bigH1)*x[0][0]-d*x[0][0]);
                    }
                    
                    else {
                        y[i_ab][i_Ab] = x[i_ab][i_Ab]+numericalstep*((ptf_fv_ab+ptf_fv_Ab-beta*full*bigZ*x[i_ab][i_Ab])+(ptf_st_0+ptf_st_1+ptf_st_2+ptf_st_3-gammaa*fullS*bigH*x[i_ab][i_Ab])+(ptf_st_4+ptf_st_5+ptf_st_6-gammaa*full2*bigH2*x[i_ab][i_Ab])+(ptf_st_7+ptf_st_8-gammaa*full1*bigH1*x[i_ab][i_Ab])-cda*x[i_ab][i_Ab]);
                    }
                } //end of popsize loop
            }
        }
    }
    return (y[N][N]);
}

//this function calculates the Gillespie propensities for each reaction
double calculatepropensities() {
    
    for (i=0; i<G; i++) {
        wnew[i] = 0;
    }
    wnew[0] = lambda; //x00 generated
    if (popsize[0][0] == 0) {
        reactsize[0] = 0;
    }
    tracker = 1;
    for (count_Ab = 0; count_Ab < N; count_Ab++) {
        for (count_ab = 0; count_ab < N-count_Ab; count_ab++) {
            if (tracker == 1) {
                wnew[tracker] = d * y[count_ab][count_Ab];
                if (popsize[count_ab][count_Ab] == 0) {
                    reactsize[tracker] = 0;
                }
                tracker++;
            }
            else {
                wnew[tracker] = cda * y[count_ab][count_Ab];
                if (popsize[count_ab][count_Ab] == 0) {
                    reactsize[tracker] = 0;
                }
                tracker++;
            }
        }
    }
        
    ptf_fv_ab = beta*(mu0*meanf_ab + mu1*meanf_Ab);
    ptf_fv_Ab = beta*(mu1*meanf_ab + mu0*meanf_Ab);

    ptf_st_0 = gammaa*syncotrans[0];
    ptf_st_1 = gammaa*syncotrans[1];
    ptf_st_2 = gammaa*syncotrans[2];
    ptf_st_3 = gammaa*syncotrans[3];
    ptf_st_4 = gammaa*syncotrans[4];
    ptf_st_5 = gammaa*syncotrans[5];
    ptf_st_6 = gammaa*syncotrans[6];
    ptf_st_7 = gammaa*syncotrans[7];
    ptf_st_8 = gammaa*syncotrans[8];
    ptf_st_9 = gammaa*syncotrans[9];

    for (count_Ab = 0; count_Ab < N-1; count_Ab++) {
        for (count_ab = 0; count_ab < N-1-count_Ab; count_ab++) {
            wnew[tracker] = ptf_fv_ab*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab+1][count_Ab] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
            wnew[tracker] = ptf_fv_Ab*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab][count_Ab+1] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
            
        }
    }
        
    for (count_Ab = 0; count_Ab < N-SS; count_Ab++) {
        for (count_ab = 0; count_ab < N-SS-count_Ab; count_ab++) {
            wnew[tracker] = ptf_st_0*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab+0][count_Ab+SS] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
            wnew[tracker] = ptf_st_1*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab+1][count_Ab+SS-1] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
            wnew[tracker] = ptf_st_2*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab+2][count_Ab+SS-2] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
            wnew[tracker] = ptf_st_3*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab+3][count_Ab+SS-3] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
        
        }
    }
    
    for (count_Ab = 0; count_Ab < N-SS+1; count_Ab++) {
        for (count_ab = 0; count_ab < N-SS+1-count_Ab; count_ab++) {
            wnew[tracker] = ptf_st_4*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab+2][count_Ab] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
            wnew[tracker] = ptf_st_5*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab+1][count_Ab+1] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
            wnew[tracker] = ptf_st_6*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab][count_Ab+2] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
           
        
        }
    }
    
    for (count_Ab = 0; count_Ab < N-SS+2; count_Ab++) {
        for (count_ab = 0; count_ab < N-SS+2-count_Ab; count_ab++) {
            wnew[tracker] = ptf_st_7*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab+1][count_Ab] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
            wnew[tracker] = ptf_st_8*y[count_ab][count_Ab];
            if (popsize[count_ab][count_Ab] == 0 || popsize[count_ab][count_Ab+1] == 0) {
                reactsize[tracker] = 0;
            }
            tracker++;
           
        
        }
    }
    return (wnew[G],reactsize[G]);
}

//this function completes the appropriate Gillespie reaction
double doreaction() {

    if (doreact[0] == 1) {
        x[0][0]++;
    }
    tracker = 1;
    for (count_Ab = 0; count_Ab < N; count_Ab++) {
        for (count_ab = 0; count_ab < N-count_Ab; count_ab++) {
            if (doreact[tracker] == 1) {
                x[count_ab][count_Ab]--;
            }
            tracker++;
        }
    }
        
    for (count_Ab = 0; count_Ab < N-1; count_Ab++) {
        for (count_ab = 0; count_ab < N-1-count_Ab; count_ab++) {
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab+1][count_Ab] == 0) {
                    x[count_ab+1][count_Ab]++;
                }
            }
            tracker++;
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab][count_Ab+1] == 0) {
                    x[count_ab][count_Ab+1]++;
                }
            }
            tracker++;
            
        }
    }

    for (count_Ab = 0; count_Ab < N-SS; count_Ab++) {
        for (count_ab = 0; count_ab < N-SS-count_Ab; count_ab++) {
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab+0][count_Ab+SS] == 0) {
                    x[count_ab+0][count_Ab+SS]++;
                }
            }
            tracker++;
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab+1][count_Ab+SS-1] == 0) {
                    x[count_ab+1][count_Ab+SS-1]++;
                }
            }
            tracker++;
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab+2][count_Ab+SS-2] == 0) {
                    x[count_ab+2][count_Ab+SS-2]++;
                }
            }
            tracker++;
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab+3][count_Ab+SS-3] == 0) {
                    x[count_ab+3][count_Ab+SS-3]++;
                }
            }
            tracker++;
           
        }
    }
    
    
    for (count_Ab = 0; count_Ab < N-SS+1; count_Ab++) {
        for (count_ab = 0; count_ab < N-SS+1-count_Ab; count_ab++) {
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab+2][count_Ab] == 0) {
                    x[count_ab+2][count_Ab]++;
                }
            }
            tracker++;
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab+1][count_Ab+1] == 0) {
                    x[count_ab+1][count_Ab+1]++;
                }
            }
            tracker++;
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab][count_Ab+2] == 0) {
                    x[count_ab][count_Ab+2]++;
                }
            }
            tracker++;
           
        }
    }
    
    for (count_Ab = 0; count_Ab < N-SS+2; count_Ab++) {
        for (count_ab = 0; count_ab < N-SS+2-count_Ab; count_ab++) {
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab+1][count_Ab] == 0) {
                    x[count_ab+1][count_Ab]++;
                }
            }
            tracker++;
            if (doreact[tracker] == 1) {
                if (popsize[count_ab][count_Ab] == 0) {
                    x[count_ab][count_Ab]--;
                }
                if (popsize[count_ab][count_Ab+1] == 0) {
                    x[count_ab][count_Ab+1]++;
                }
            }
            tracker++;
           
        }
    }
    return (x[N][N]);
}


//main program (this is the beginning of the main program)
int main(int argc, const char * argv[]) {
    FILE *file_handle;
    std::mt19937_64 mt_rand(time(0));
    std::default_random_engine generator(time(0));
    std::uniform_real_distribution<double> distribution(0.0,1.0);
        
    for (loops = 0; loops < numberofloops; loops++) {
        t = 0;
        told = 0;
        htemp = 0;
        save = 0;
        infected = 0;
        bigZ = 0;
        bigH = 0;
        bigH2 = 0;
        bigH1 = 0;
        
        //initial conditions
        for (i_ab=0; i_ab<N; i_ab++) {
            for (i_Ab=0; i_Ab<N; i_Ab++) {
                x[i_ab][i_Ab] = 0;
            }
        }
        x[0][0] = lambda / d;
        x[1][0] = 1;
        
        while (infected < sizestop) { //loop that runs for each simulation until the stopping size of infected cells is reached
            for (i=0; i<G; i++) {
                integral[i] = 0;
                randomprob = distribution(generator);
                logr[i] = log(randomprob);
                doreact[i] = 0;
                reactsize[i] = 1;
                timecalcold[i] = logr[i];
                tau[i] = 100000000;
            }
            
            for (i_ab=0; i_ab<N; i_ab++) {
                for (i_Ab=0; i_Ab<N; i_Ab++) {
                    if (x[i_ab][i_Ab] < M) {
                        popsize[i_ab][i_Ab]= 0;
                        y[i_ab][i_Ab] = x[i_ab][i_Ab]; //0
                    }
                    else {
                        popsize[i_ab][i_Ab] = 1;
                        y[i_ab][i_Ab] = x[i_ab][i_Ab];
                    }
                }
            }
            
            calculatesubpopulations();
            
            if (infected == 0) {
                //printf("INFECTION DIED OUT \n");
                break;
            }
 
            calculatepropensities();
            infected = 0;
            
            while (infected < sizestop) { //loop that runs for each simulation until the stopping size of infected cells is reached
                for (i=0; i<G; i++) {
                    wold[i] = wnew[i];
                }
                
                numericalstep(h);
                
                for (i_ab=0; i_ab<N; i_ab++) { //loop that makes sure no populations are negative (possible from the loss of a cell in a Gillespie reaction in a population that < 1)
                    for (i_Ab=0; i_Ab<N; i_Ab++) {
                        if (y[i_ab][i_Ab] < 0) {
                            y[i_ab][i_Ab] = 0;
                        }
                    }
                }
                
                calculatesubpopulations();
                calculatepropensities();

                stop = 0;
                for (i=0; i<G; i++) { //loop that calculates the time integrals and decides whether it is time for a stochastic event
                    if (reactsize[i] == 0) {
                        integral[i] = integral[i] + (wold[i] + wnew[i]) * h / 2;
                        timecalcnew[i] = integral[i] + logr[i];
                        if (timecalcnew[i] > 0) {
                            tau[i] = t - timecalcold[i] / wold[i];
                            stop = 1;
                        }
                    }
                }
                
                if (stop == 1) {
                    calclocation = 0;
                    minn = tau[0];
                    
                    for (i=1; i<G; i++) {
                        if (tau[i] < minn) {
                            calclocation = i;
                            minn = tau[i];
                        }
                    }

                    doreact[calclocation] = 1;
                    t = minn;
                    htemp = t - told;
                    calculatesubpopulations();
                    numericalstep(htemp);
                    
                    for (i_ab=0; i_ab<N; i_ab++) {
                        for (i_Ab=0; i_Ab<N; i_Ab++) {
                            x[i_ab][i_Ab] = y[i_ab][i_Ab];
                        }
                    }
                    break;
                }
                
                for (i=0; i<G; i++) {
                    timecalcold[i] = timecalcnew[i];
                }

                for (i_ab=0; i_ab<N; i_ab++) {
                    for (i_Ab=0; i_Ab<N; i_Ab++) {
                        x[i_ab][i_Ab] = y[i_ab][i_Ab];
                    }
                }

                t = t+h;
                told = t;
                  
            } //end of numerical loop

            doreaction();

            for (i_ab=0; i_ab<N; i_ab++) { //loop that makes sure no populations are negative (possible from the loss of a cell in a Gillespie reaction in a population that < 1)
                for (i_Ab=0; i_Ab<N; i_Ab++) {
                    if (y[i_ab][i_Ab] < 0) {
                        y[i_ab][i_Ab] = 0;
                    }
                }
            }
        } //end of t loop
        
        multN = 0;

        for (i_ab=0; i_ab<N; i_ab++) { //loop that calculates how many cells have reach maximum infection multiplicity
            for (i_Ab=0; i_Ab<N; i_Ab++) {
                if ((i_ab + i_Ab) == N-1) {
                    multN = multN + x[i_ab][i_Ab];
                }
            }
        }
        
        calculatesubpopulationstoprint();

        if (infected > 0) {
            file_handle = fopen(filename.c_str(), "a"); //if not working then change your permissions or add full file path
            fprintf(file_handle, "%lf, %lf, %lf \n", M, t, actualinfected_Ab);
            fclose(file_handle);
        }
    } //end of loop loop
    return 0;
}




