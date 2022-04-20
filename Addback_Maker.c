#include <iostream>
#include <string>
#include <sstream>
#include <iomanip>
#include <fstream>
#include <limits>
#include <stdio.h>
#include <stdlib.h>
#include <TFile.h>
#include <TTree.h>
#include <TH2.h>
#include <TH1.h>
#include <TF1.h>
#include <TCutG.h>
#include <TCanvas.h>
#include <TChain.h>
#include <TFitResult.h>
#include <TLegend.h>
#include <TMath.h>
#include <TGraphErrors.h>
#include <TMultiGraph.h>
#include <TSpectrum.h>
#include <TROOT.h>
#include <TPolyMarker.h>
#include <TLine.h>
#include <GStyle.h>

using namespace std;



void printProgBar(float percent){
  std::string bar;

  for(int i=0;i<50;i++){
    if(i<(int(percent)/2))bar.replace(i,1,"=");
    else if(i==int(percent/2)) bar.replace(i,1,">");
    else bar.replace(i,1," ");
  }

  std::cout << "\r [" << bar << "]";
  std::cout.width(3);
  std::cout<< std::fixed;
  std::cout<< std::setprecision(2);
  std::cout<< percent << "%"<< std::flush;
}

void Addbacker(bool Take_Diagonal = true, string outfname=""){

  // Addback procedure macro
  // To start the addback procedure, load the macro and use Addbacker()
  //
  // A file with the path to all data file to be used needs to be in the same directory and to be named "filename.dat"
  // A file with all paris PSD gates needs to be in the same directory and to be named "PSD_gate.txt"
  // A file with calibration coefficients for LaBr3 detectors needs to be in the same directory and to be named "Calibration_Coef.txt"
  // A file with the graphical cuts for the alpha events selection needs to be in the same directory and to be named "sel_monster_n.root"
  //
  // In addition this function can take two optionnal arguments :
  //    - bool Take_Diagonal : If set to false, only paris detectors directly touching (having a face in common) are considered as neighbors. Otherwise, diagonal detectors are also considered as neighbors. If diagonal detectors are considered as neighbors, the add back should be more efficient, but the risk of adding true coincidences is higher. Tests seems to indicate that taking diagonal detectors as neighbors is a better solution, thus it is recommended to set this to true. It is set to true by default
  //    - string outfname : If a non empty string is given here, a root file named as the string will be created. It will contain all the histograms created by the code. By default it is set to an empty string and thus the histograms are not saved.

  gStyle->SetOptStat(0);

  const double ch_min = 0;
  const double ch_max = 1.2e4;
  const int nbins = 3e3;
  const double ch_per_bin = (ch_max - ch_min)/nbins;

  double time_window = 7e3; ///time window for one physical event (in ps) (2ns is probably better than the current 7ns value)

  // Defining 2 adjacent matrix, one considering diagonal paris as neighbors, the other considering only directly touching detectors as neighbors
  int adj_matrix[18][18]= {
    {1,1,0,1,0,0,0,0,0, 0,0,0,0,0,0,0,0,0},
    {1,1,1,0,1,0,0,0,0, 0,0,0,0,0,0,0,0,0},
    {0,1,1,0,0,1,0,0,0, 0,0,0,0,0,0,0,0,0},
    {1,0,0,1,1,0,1,0,0, 0,0,0,0,0,0,0,0,0},
    {0,1,0,1,1,1,0,1,0, 0,0,0,0,0,0,0,0,0},
    {0,0,1,0,1,1,0,0,1, 0,0,0,0,0,0,0,0,0},
    {0,0,0,1,0,0,1,1,0, 0,0,0,0,0,0,0,0,0},
    {0,0,0,0,1,0,1,1,1, 0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,1,0,1,1, 0,0,0,0,0,0,0,0,0},

    {0,0,0,0,0,0,0,0,0, 1,1,0,1,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0, 1,1,1,0,1,0,0,0,0},
    {0,0,0,0,0,0,0,0,0, 0,1,1,0,0,1,0,0,0},
    {0,0,0,0,0,0,0,0,0, 1,0,0,1,1,0,1,0,0},
    {0,0,0,0,0,0,0,0,0, 0,1,0,1,1,1,0,1,0},
    {0,0,0,0,0,0,0,0,0, 0,0,1,0,1,1,0,0,1},
    {0,0,0,0,0,0,0,0,0, 0,0,0,1,0,0,1,1,0},
    {0,0,0,0,0,0,0,0,0, 0,0,0,0,1,0,1,1,1},
    {0,0,0,0,0,0,0,0,0, 0,0,0,0,0,1,0,1,1}
  };

  int adj_matrix_diagonal[18][18] = {
    {1,1,0,1,1,0,0,0,0, 0,0,0,0,0,0,0,0,0},
    {1,1,1,1,1,1,0,0,0, 0,0,0,0,0,0,0,0,0},
    {0,1,1,0,1,1,0,0,0, 0,0,0,0,0,0,0,0,0},
    {1,1,0,1,1,0,1,1,0, 0,0,0,0,0,0,0,0,0},
    {1,1,1,1,1,1,1,1,1, 0,0,0,0,0,0,0,0,0},
    {0,1,1,0,1,1,0,1,1, 0,0,0,0,0,0,0,0,0},
    {0,0,0,1,1,0,1,1,0, 0,0,0,0,0,0,0,0,0},
    {0,0,0,1,1,1,1,1,1, 0,0,0,0,0,0,0,0,0},
    {0,0,0,0,1,1,0,1,1, 0,0,0,0,0,0,0,0,0},

    {0,0,0,0,0,0,0,0,0, 1,1,0,1,1,0,0,0,0},
    {0,0,0,0,0,0,0,0,0, 1,1,1,1,1,1,0,0,0},
    {0,0,0,0,0,0,0,0,0, 0,1,1,0,1,1,0,0,0},
    {0,0,0,0,0,0,0,0,0, 1,1,0,1,1,0,1,1,0},
    {0,0,0,0,0,0,0,0,0, 1,1,1,1,1,1,1,1,1},
    {0,0,0,0,0,0,0,0,0, 0,1,1,0,1,1,0,1,1},
    {0,0,0,0,0,0,0,0,0, 0,0,0,1,1,0,1,1,0},
    {0,0,0,0,0,0,0,0,0, 0,0,0,1,1,1,1,1,1},
    {0,0,0,0,0,0,0,0,0, 0,0,0,0,1,1,0,1,1}
  };

  if(Take_Diagonal){
    for(int i=0;i<18;i++){
      for(int j=0;j<18;j++){
        adj_matrix[i][j] = adj_matrix_diagonal[i][j];
      }
    }
  }

  vector<double> gate_inf_LaBr3, gate_sup_LaBr3, gate_inf_NaI, gate_sup_NaI;

  ifstream PSDin("PSD_gate.txt", ios::in | ios::binary); ///open the file containing PSD gates ...

  string line;
  stringstream linestream;
  int det, i=0;
  double temp1, temp2, temp3, temp4, temp5; ///definition of temporary variables

  while(PSDin.good()){ ///... read PSD_gates file

    getline(PSDin, line); ///read one line of the file and save it in the string "line", go to the next line
    linestream.clear();  ///clear the object "linestream"
    linestream.str(line); ///convert the string into streamstring

    if (linestream.fail() or line.empty()) continue; ///if the line is empty or not convertible, continue

    if (line.find("#") != string::npos) continue; ///# at the beginning of the line => ignore it

    linestream >> temp1 >> temp2 >> temp3 >> temp4 >> temp5; ///each object of the line (here 5 : see the PSD_gates.txt) is stored in a temporary variable...
    gate_inf_LaBr3.push_back(temp2); ///... each temporary variable is stored in the right place of the list containing the gates.
    gate_sup_LaBr3.push_back(temp3);
    gate_inf_NaI.push_back(temp4);
    gate_sup_NaI.push_back(temp5);
  }

  PSDin.close();


  ifstream Calibin("Calibration_Coef.txt", ios::in | ios::binary); ///open the file containing the calibration coefficients



  int rightline = 0;
  vector<double> a_LaBr3, b_LaBr3;
  while(Calibin.good()){ ///... read read the calibration file
    string temp6;
    getline(Calibin, line); ///read one line of the file and save it in the string "line", go to the next line
    linestream.clear();  ///clear the object "linestream"
    linestream.str(line); ///convert the string into streamstring

    if (linestream.fail() or line.empty()) continue; ///if the line is empty or not convertible, continue

    if (line.find("#") != string::npos) continue; ///# at the beginning of the line => ignore it

    if(rightline%2 != 0 or rightline>34){
      rightline++;
      continue;
    }
    rightline++;
    linestream >> temp6 >> temp2 >> temp3; ///each object of the line is stored in a temporary variable...
    b_LaBr3.push_back(temp2);
    a_LaBr3.push_back(temp3);
  }

  Calibin.close();


  ifstream files("filename.dat", ios::in | ios::binary); ///open the file containing the path to the data files...
  TChain *tin = new TChain("DataTree","Datatree");


  while(files.good()){ ///... read filename file

    getline(files, line); ///read one line of the file and save it in the string "line", go to the next line

    if (line.empty()) continue; ///if the line is empty or not convertible, continue

    if (line.find("#") != string::npos) continue; ///# at the beginning of the line => ignore it

    tin->Add(line.c_str()); //Add the file to the chain
  }

  files.close();

  vector<TCutG*> Cuts;



  TFile *f = new TFile("./sel_monster_n.root","read"); // Getting the graphical cuts to isolate the alpha in monster

  Cuts.push_back((TCutG*)f->Get("Cut_alpha_23"));
  Cuts.push_back((TCutG*)f->Get("Cut_alpha_24"));
  Cuts.push_back((TCutG*)f->Get("Cut_alpha_25"));
  Cuts.push_back((TCutG*)f->Get("Cut_alpha_26"));
  Cuts.push_back((TCutG*)f->Get("Cut_alpha_27"));
  Cuts.push_back((TCutG*)f->Get("Cut_alpha_28"));


  // Creation of variables to hold the tree datas
  vector<int> *Q1 = 0;
  vector<int> *Q2 = 0;
  vector<int> *Q3 = 0;
  vector<int> *Q4 = 0;
  vector<ULong64_t> *time = 0;
  vector<unsigned char> *label = 0;
  vector<bool> *pu = 0;
  UShort_t multiplicity;
  vector<float> *Q1_cal = 0;
  vector<float> *Q2_cal = 0;

  tin->SetBranchAddress("label",&label);
  tin->SetBranchAddress("nrj1",&Q1);
  tin->SetBranchAddress("nrj2",&Q2);
  tin->SetBranchAddress("nrj3",&Q3);
  tin->SetBranchAddress("nrj4",&Q4);
  tin->SetBranchAddress("time",&time);
  tin->SetBranchAddress("pileup",&pu);
  tin->SetBranchAddress("multiplicity",&multiplicity);
  tin->SetBranchAddress("nrj1_cal",&Q1_cal);
  tin->SetBranchAddress("nrj2_cal",&Q2_cal);


  // Histo initialisation
  TH1I *labels = new TH1I("labels","labels",40,0,40); // Number of hit per label. One can obtain the total charge through channel 31


  TH1F *hc1 = new TH1F("hc1","Gamma Spectrum in Paris cluster 1 without AddBack;Egamma (keV);Counts/4keV",nbins,ch_min,ch_max);
  TH1F *hc2 = new TH1F("hc2","Gamma Spectrum in Paris cluster 2 without AddBack;Egamma (keV);Counts/4keV",nbins,ch_min,ch_max);
  
  TH1F *hadd1 = new TH1F("hadd1","Gamma Spectrum in Paris cluster 1 with AddBack;Egamma (keV);Counts/4keV",nbins,ch_min,ch_max);
  TH1F *hadd2 = new TH1F("hadd2","Gamma Spectrum in Paris cluster 2 with AddBack;Egamma (keV);Counts/4keV",nbins,ch_min,ch_max);

  TH1F *hg = new TH1F("hg","Gamma Spectrum in Paris without AddBack;Egamma (keV);Counts/4keV",nbins,ch_min,ch_max);
  TH1F *hadd = new TH1F("hadd","Gamma Spectrum in Paris with AddBack;Egamma (keV);Counts/4keV",nbins,ch_min,ch_max);
  TH1F *hsel = new TH1F("hsel","Gamma Spectrum in Paris with AddBack and emitted in coincidence with a source interaction;Egamma (keV);Counts/4keV",nbins,ch_min,ch_max);
  TH1F *hdiag = new TH1F("hdiag","Gamma Spectrum in Paris with Egamma=Estar;Egamma (keV);Counts/4keV",nbins,ch_min,ch_max);
  TH1F *hToFParis = new TH1F("hToFParis","ToF for all Paris detectors;ToF(ns);Counts/0.1ns",3000,-100,200);
  TH1F *hToFMonsterN = new TH1F("hToFMonsterN","Neutron ToF for all Monster detectors;ToF(ns);Counts/0.1ns",6000,-100,500);
  TH1F *hToFMonsterNParis = new TH1F("hToFMonsterNParis","Neutron ToF for all Monster detectors with Paris as time reference;ToF(ns);Counts/0.1ns",6000,-100,500);
  TH1F *hToFMonsterNcoinc = new TH1F("hToFMonsterNcoinc","Neutron ToF for all Monster detectors selected with a gamma in coinc in Paris;ToF(ns);Counts/0.1ns",6000,-100,500);
  TH1F *hToFMonsterG = new TH1F("hToFMonsterG","Gamma ToF for all Monster detectors;ToF(ns);Counts/0.1ns",6000,-100,500);
  TH1F *hToFMonsterA = new TH1F("hToFMonsterA","Alpha ToF for all Monster detectors;ToF(ns);Counts/0.1ns",6000,-100,500);
  TH1F *hToFMonster = new TH1F("hToFMonster","All ToF for all Monster detectors;ToF(ns);Counts/0.1ns",6000,-100,500);

  TH1F *hdt = new TH1F("hdt","Delta t between events in Paris;Delta T (ns);Counts/0.1ps",600,-30,30);

  vector<TH1D*> hmonster,ToFmonsterN,ToFmonsterG,ToFmonsterAlpha,Emonster,ToFParis,Calib_LaBr3,Calib_NaI;

  TH2D * EgammaEstar = new TH2D("EgammaEstar","E gamma vs Estar;Estar (keV);Egamma (keV)",350,0,14000,1200,0,12000);
  TH2D * ToFgammaEstar = new TH2D("ToFgammaEstar","ToF gamma vs Estar;Estar;ToFgamma (ns)",3000,0,30000,5000,-100,4000);
  TH2D * ToFgammaToFneutron = new TH2D("ToFgammaToFneutron","ToF gamma vs ToFneutron;ToFneutron (ns);ToFgamma (ns)",4000,-100,300,5000,-100,400);
  TH2D * EgammaToF = new TH2D("EgammaToF","E gamma vs ToF neutron;ToF neutron (ns) ;Egamma",5000,-100,400,1200,0,12000);
  TH2D * EgammaToFgamma = new TH2D("EgammaToFgamma","E gamma vs ToF gamma;ToF gamma (ns);Egamma (keV)",1000,-100,400,600,0,12000);


  vector<TH2D*> MonsterPSDToF, MonsterPSDToFAlpha, MonsterPSDToFNeutron, MonsterPSD, ParisPSD;


  long long time_shifts[6] = {-322519,-322363,-322899,-322702,-322705,-323117}; // Time shift between RF and monster detectors
  double dists_monster[6] = {3039.7,3036.1,3033.7,3032.0,3028.6,3025.8}; // Distances between monster detectors and target
  double dist_conv_target = 4905.2; // Distance between convertor and target
  double PSDMonster[6] = {0.14,0.14,0.14,0.14,0.15,0.15}; // Threshold for monster psd


  for(int i=0;i<18;i++){
    ToFParis.push_back(new TH1D(TString::Format("ToF N det %d",i+1),TString::Format("ToF N det %d;ToF gamma (ns);Counts/0.1ns",i+1),5000,-100,400));
    Calib_LaBr3.push_back(new TH1D(TString::Format("Paris LaBr3 %d",i+1),TString::Format("Paris LaBr3 %d",i+1),12000,0,12000));
    Calib_NaI.push_back(new TH1D(TString::Format("Paris NaI %d",i+1),TString::Format("Paris NaI %d",i+1),2000,0,1000000));
    ParisPSD.push_back(new TH2D(TString::Format("ParisPSD det %d",i),TString::Format("Paris PSD vs Qlong det %d;Qlong;(Qlong-Qshort)/Qlong",i),1000,0,1000000,700,-0.2,1.2));
  }


  for(int i=23;i<29;i++){
    hmonster.push_back(new TH1D(TString::Format("Det %d",i),TString::Format("Det %d",i),3000,0,30000));
    ToFmonsterN.push_back(new TH1D(TString::Format("ToF N det %d",i),TString::Format("ToF N det %d;ToF neutron (ns);Counts/0.1ns",i),5000,-400,600));
    ToFmonsterG.push_back(new TH1D(TString::Format("ToF G det %d",i),TString::Format("ToF G det %d;ToF gamma (ns);Counts/0.1ns",i),5000,-400,600));
    ToFmonsterAlpha.push_back(new TH1D(TString::Format("ToF alpha det %d",i),TString::Format("ToF alpha det %d;ToF neutron (ns);Counts/0.1ns",i),5000,-400,600));
    Emonster.push_back(new TH1D(TString::Format("E det %d",i),TString::Format("E det %d",i),400,0,40000));
    MonsterPSDToF.push_back(new TH2D(TString::Format("MonsterPSDToF det %d",i),TString::Format("Monster PSD vs ToF det %d;ToF (ns); Qdelayed/Qlong",i),2000,0,200,400,-0.2,0.6));
    MonsterPSDToFAlpha.push_back(new TH2D(TString::Format("MonsterPSDToF alpha det %d",i),TString::Format("Monster PSD vs ToF alpha det %d;ToF (ns);Qdelayed/Qlong",i),2000,0,200,400,-0.2,0.6));
    MonsterPSDToFNeutron.push_back(new TH2D(TString::Format("MonsterPSDToF neutron det %d",i),TString::Format("Monster PSD vs ToF neutron det %d;ToF (ns);Qdelayed/Qlong",i),2000,0,200,400,-0.2,0.6));
    MonsterPSD.push_back(new TH2D(TString::Format("MonsterPSD det %d",i),TString::Format("Monster PSD vs Qlong det %d;Qlong;Qdelayed/Qlong",i),1000,0,300000,400,-0.2,0.6));
  }

  int nentries = (Int_t)tin->GetEntries();
  double tf = 0, ti = 1e10;
  int ntref0 = 0, ntref=0;
  long charge = 0;


  cout << "Reading the Tree ..." << endl;
  // Reading the tree, addback procedure and filling of the histograms
  for(int entry=0 ; entry<nentries ; entry++) {

    tin->GetEntry(entry);

    int physical_multiplicity = 0; // Hold the multiplicity after AddBack

    int processed_events[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}; // Hold if a given event was already treated

    vector<ULong64_t> time_monster_gamma,time_monster_neutron,time_monster;
    vector<int> label_monster_gamma, label_monster_neutron, label_monster;

    int meas_mult_gamma = 0;

    vector<double> Eneutron, Egamma, ToFneutron,ToFgamma, Tneutron, Tgamma ,Q2monster, Q3monster;
    vector<int> LNeutron, Lgamma;

    double tref_hf = 0;

    for(int i=0;i<(int)multiplicity;i++){
      if(label->at(i)==29){
        tref_hf = time->at(i); // RF time
        break;
      }
    }
    
    // Start of Add-back procedure
    for(int i=0 ; i < (int)multiplicity ; i++){ //Addback loop
      labels->Fill(label->at(i));
      if(label->at(i)==31){
        charge++;
      }

      if(time->at(i)/1000000000000.>tf) tf = time->at(i)/1000000000000.;// Obtention of the last time stamp (s)
      if(time->at(i)/1000000000000.<ti) ti = time->at(i)/1000000000000.;// Obtention of the first time stamp (s)

      if(label->at(i)<19){
        long long tof_gamma_paris = 750; // Gamma time of flight between target and paris detectors (ps)
        long long time_shift_paris = -323037; // Time shift between rf and paris detectors

        if(time->at(i)-tref_hf-time_shift_paris+tof_gamma_paris>-1000 and time->at(i)-tref_hf-time_shift_paris+tof_gamma_paris<2000) meas_mult_gamma++;
        if(processed_events[i]==1) continue; // If the event was already processed, continue

        processed_events[i] = 1; // Otherwise, process the event
        float temp_e = 0;
        float physical_E = 0;

        unsigned char physical_label = label->at(i); // For now the physical label
        ULong64_t physical_time = time->at(i); // For now the physical time
        double ratio = (double(Q2->at(i)) - double(Q1->at(i)))/double(Q1->at(i)); // Paris psd

        ParisPSD[label->at(i) - 1]->Fill(Q2->at(i),ratio); // Fill PSD histo
        if (ratio > gate_inf_LaBr3[label->at(i) - 1] and ratio < gate_sup_LaBr3[label->at(i) - 1]){ // if LaBr3 event, use LaBr3 calibration

          //physical_E = (float)Q1_cal->at(i); // If the data are already properly calibrated, use this
          physical_E = (float)Q1->at(i)*a_LaBr3[label->at(i)-1]+b_LaBr3[label->at(i)-1]; // Use the calibration in the calibration file
          temp_e=physical_E; // Hold the highest energy deposit
          hg->Fill(physical_E); // Fill a calibrated total gamma histo
          Calib_LaBr3[label->at(i) - 1]->Fill((float)Q1->at(i)*a_LaBr3[label->at(i)-1]+b_LaBr3[label->at(i)-1]); // Fill one gamma histo per detector
          if(label->at(i)-1<9){
            hc1->Fill((float)Q1->at(i)*a_LaBr3[label->at(i)-1]+b_LaBr3[label->at(i)-1]);
          }
          else if(label->at(i)-1<18){
            hc2->Fill((float)Q1->at(i)*a_LaBr3[label->at(i)-1]+b_LaBr3[label->at(i)-1]);
          }
        }
        else if (ratio > gate_inf_NaI[label->at(i) - 1] and ratio < gate_sup_NaI[label->at(i) - 1]){ // Same as before be for NaI
          physical_E = (float)Q2_cal->at(i);
          temp_e=physical_E;
          hg->Fill(physical_E);
          Calib_NaI[label->at(i) - 1]->Fill((float)Q2->at(i));

        }

        for(int j=i+1 ; j<(int)multiplicity ; j++){ // Check if another event should be added by the addback procedure

          if(label->at(j)>18) continue; // Monster detectors are not to be considered
          if (processed_events[j] == 1) continue; // If the event was already processed, it should not be considered

          double delta_t = abs(double(time->at(i)) - double(time->at(j))); // Compute the time difference between the two events
          
          hdt->Fill((double(time->at(i)) - double(time->at(j)))/1000.);

          if(delta_t<time_window and adj_matrix[label->at(i) - 1][label->at(j) - 1]!=0){ // If the event is within the time window and the detectors are neighbors, the events should be added

            processed_events[j] = 1; // The event is now processed
            ratio = (double(Q2->at(j)) - double(Q1->at(j)))/double(Q1->at(j)); // Compute PSD for Paris

            if (ratio > gate_inf_LaBr3[label->at(j) - 1] and ratio < gate_sup_LaBr3[label->at(j) - 1]){ // If LaBr3 event
              //physical_E += (float)Q1_cal->at(j);
              physical_E += (float)Q1->at(j)*a_LaBr3[label->at(j)-1]+b_LaBr3[label->at(j)-1]; // Add the energy to the previous one
              Calib_LaBr3[label->at(j) - 1]->Fill((float)Q1->at(j)*a_LaBr3[label->at(j)-1]+b_LaBr3[label->at(j)-1]); // Fill one gamma histo per detector
              if(temp_e < (float)Q1_cal->at(j)){ //If the second energy deposit is higher than the first one, take the second as the physical event
                physical_label = label->at(j);
                physical_time = time->at(j);
                //temp_e = (float)Q1_cal->at(j);
                temp_e = (float)Q1->at(j)*a_LaBr3[label->at(j)-1]+b_LaBr3[label->at(j)-1];
              }
              
              if(label->at(i)-1<9){
                hc1->Fill((float)Q1->at(i)*a_LaBr3[label->at(i)-1]+b_LaBr3[label->at(i)-1]);
              }
              else if(label->at(i)-1<18){
                hc2->Fill((float)Q1->at(i)*a_LaBr3[label->at(i)-1]+b_LaBr3[label->at(i)-1]);
              }

            }
            else if (ratio > gate_inf_NaI[label->at(j) - 1] and ratio < gate_sup_NaI[label->at(j) - 1]){ // If NaI event
              physical_E += (float)Q2_cal->at(j); // Add the energy to the previous one
              Calib_NaI[label->at(j) - 1]->Fill((float)Q2->at(j)); // Fill one gamma histo per detector
              if(temp_e < (float)Q2_cal->at(j)){ //If the second energy deposit is higher than the first one, take the second as the physical event
                physical_label = label->at(j);
                physical_time = time->at(j);
                temp_e = (float)Q2_cal->at(j);
              }
            }
          }
        }

        if(physical_E>0){ // If the physical energy is not zero, add the event to the list of events

          long long dt = physical_time-tref_hf-time_shift_paris+tof_gamma_paris; // Compute the time stamp of the event with the target interaction as the 0 point in time
          hadd->Fill(physical_E); // Fill an histogram with the physical energy
          if(physical_label-1<9) hadd1->Fill(physical_E);
          else if(physical_label-1<18) hadd2->Fill(physical_E);
          if(dt>-1000 and dt<2000) hsel->Fill(physical_E); // Fill an histogram with the physical energy form promt gammas
          Egamma.push_back(physical_E); // Make a list of physical energies
          ToFParis[physical_label-1]->Fill(dt/1000.); // Fill an histogram per detector with the time stamp of the events (ns)
          hToFParis->Fill(dt/1000.); // Fill an histogram with allt the time stamps of the events (ns) for all detectors
          ToFgamma.push_back(dt); // Make a list of time stamps
          Lgamma.push_back(physical_label); // Make a list of physical label
          Tgamma.push_back(physical_time-time_shift_paris); // Make a list of time stamps without taking the RF as reference
        }
      } 
      // End of Add-back procedure

      else if(label->at(i)>22 and label->at(i)<29){ // If the event is in a monster detector
        if(tref_hf==0) { // Check that time reference is not 0. If it is zero continue
          ntref0++;
          continue;
        }
        ntref++;
        double Qtemp2 = Q2->at(i), Qtemp3 = Q3->at(i); // Get the Qlong and Qdelayed

        double c = 0.299792458; // Light celerity in mm.ps-1
        double d = dists_monster[label->at(i)-23]; // Distance between the target and the detectors in mm
        double Mn = 939565.4; // Neutron mass in keV/c2
        double v,beta, Ec, gamma;
        double t0 = time->at(i);

        double dt = t0-tref_hf;
        double ToFn = dt - time_shifts[label->at(i)-23] + (d/c); // Time of flight of the neutron from the target to the monster detector in ps

        MonsterPSD[label->at(i)-23]->Fill(Qtemp2,Qtemp3/Qtemp2); // Fill Monster PSD 2D histo for each detector
        MonsterPSDToF[label->at(i)-23]->Fill(ToFn/1000.,Qtemp3/Qtemp2); // Fill Monster PSD vs ToF 2D histo for each detector

        hToFMonster->Fill(ToFn/1000.); // Fill time of flight histo for each monster

        if(Cuts[label->at(i)-23]->IsInside(Qtemp2,Qtemp3/Qtemp2)){ // if the event is inside an alpha cut
          
          ToFmonsterAlpha[label->at(i)-23]->Fill(ToFn/1000.); // Fill ToF histo for alpha events
          MonsterPSDToFAlpha[label->at(i)-23]->Fill(ToFn/1000.,Qtemp3/Qtemp2); // Fill PSD vs ToF histo for alpha events
          hToFMonsterA->Fill(ToFn/1000.); // Fill toF histo for alpha events
          
        }
        if(Qtemp3/Qtemp2>PSDMonster[label->at(i)-23] and ToFn>38000){ // PSD and time of flight selection to get only neutron event
          hmonster[label->at(i)-23]->Fill(Q2_cal->at(i)); // Fill an histo per detector with monster detected energy
          ToFmonsterN[label->at(i)-23]->Fill(ToFn/1000.); // Fill an histo per detector with neutron ToF
          hToFMonsterN->Fill(ToFn/1000.); // Fill an histo with all neutron ToF
          MonsterPSDToFNeutron[label->at(i)-23]->Fill(ToFn/1000.,Qtemp3/Qtemp2); // Fill a PSD vs ToF histo for neutron events
          v = d/ToFn; // neutron speed in mm.ps-1
          beta = v/c; // beta factor of the neutron
          gamma = 1/TMath::Sqrt(1-(beta*beta)); // Lorentz factor for the neutron
          Ec = Mn*(gamma-1); // Kinetic energy of the neutron

          if(Ec>10){ // If the kinetic energy is above 10keV (avoid a very large first bin in the histograms)
            LNeutron.push_back(label->at(i)); // Make a list of neutron events labels
            Eneutron.push_back(Ec); // Make a list of neutron kinetic energy
            ToFneutron.push_back(ToFn); // Make a list of neutron time of flight
            Tneutron.push_back(t0 - time_shifts[label->at(i)-23] + (d/c)); // Make a list of neutron time stamps without using RF as time reference
            Emonster[label->at(i)-23]->Fill(Ec); // Fill an histogram per detector with neutron kinetic energies
          }
          
        }
        else{ // If none of the above condition are verified, the event is considered as a gamma event
          ToFmonsterG[label->at(i)-23]->Fill(ToFn/1000.); // Fill a ToF histogram per detector
          hToFMonsterG->Fill(ToFn/1000.); // Fill a ToF histogram for all detectors
        }
      }
    }
    
    // End of multiplicity loop

    for(int i=0;i<Eneutron.size();i++){ // For each detected neutron
      bool first = true;
      double v,beta, Ec, gamma;
      double c = 0.299792458; // Light celerity in mm.ps-1
      double d = dists_monster[LNeutron[i]-23]; // Distance between the target and the detectors in mm
      double Mn = 939565.4; // Neutron mass in keV/c2
      for(int j=0;j<Egamma.size();j++){ // For each gamma detected in coinc with a neutron
        v = d/(Tneutron[i]-Tgamma[j]); // compute the speed of the neutron (mm.ps-1) using paris as a time reference
        beta = v/c; // Compute the beta factor
        gamma = 1/TMath::Sqrt(1-(beta*beta)); // Lorentz factor
        Ec = Mn*(gamma-1); // Neutron kinetic energy

        ToFgammaEstar->Fill(30850.-Ec,ToFgamma[j]); // Fill Gamma time of flight vs exitation energy histogram
        ToFgammaToFneutron->Fill(ToFneutron[i]/1000.,ToFgamma[j]/1000.); // Fill gamma time of flight ws neutron time of flight histo
        EgammaToFgamma->Fill(ToFgamma[j]/1000.,Egamma[j]); // Fill gamma energy vs gamma time of flight histo
        if(ToFgamma[j]<-1500 or ToFgamma[j]>3000) continue; // If the gamma is a prompt gamma
        //EgammaEstar->Fill(30850.-Eneutron[i],Egamma[j]); // Fill gamma energy vs exitation energy histogram. Neutron ToF used for energy computation is the one with the RF as a time reference
        EgammaEstar->Fill(30850.-Ec,Egamma[j]); // Fill gamma energy vs exitation energy histogram. Neutron ToF used for energy computation is the one with paris as a time reference
        EgammaToF->Fill(ToFneutron[i]/1000.,Egamma[j]); // Gamma energy vs neutron time of flight
        if(abs(30850.-Ec-Egamma[j])<1600) hdiag->Fill(Egamma[j]); // If the exitation energy and the gamma energy are within 1.6MeV of each other, fill and histo with gamma energy
        if(first){
          hToFMonsterNcoinc->Fill(ToFneutron[i]/1000.);
          hToFMonsterNParis->Fill((Tneutron[i]-Tgamma[j])/1000.);
          first = false;
        }
      }
    }

if(entry%10000==0) printProgBar(entry*100.0/nentries); // print a progression bar

}

cout << endl;


// start plotting all histogram
auto c0 = new TCanvas("label","label");
labels->Draw("hist");

auto c1 = new TCanvas("AddBack","Addback");
hadd->SetLineColor(3);
hadd->Draw("hist");
hg->SetLineColor(2);
hg->Draw("hist same");
hsel->Draw("hist same");

c1->Update();
auto legend3 = new TLegend(.7,.78,.9,.9);
legend3->AddEntry(hg,"All gammas in paris","l");
legend3->AddEntry(hadd,"All gammas in paris with addback","l");
legend3->AddEntry(hsel,"Prompt gammas in paris with addback","l");
legend3->Draw();

auto c2 = new TCanvas("Selected gammas","Selected gammas");
hsel->Draw("hist");

auto cToFParis = new TCanvas("All ToF Paris","All ToF Paris");
hToFParis->Draw("hist");
auto l5 = new TLine(-1.5,0,-1.5,hToFParis->GetMaximum()*1.05);
l5->SetLineColor(2);
l5->SetLineWidth(2);
l5->Draw("same");
auto l6 = new TLine(3.,0,3,hToFParis->GetMaximum()*1.05);
l6->SetLineColor(2);
l6->SetLineWidth(2);
l6->Draw("same");

auto cToFMonster = new TCanvas("ToF All Monster","ToF All Monster");
//hToFMonster->Draw("hist");
//hToFMonsterA->SetLineColor(2);
//hToFMonsterA->Draw("hist same");
//hToFMonsterG->SetLineColor(3);
//hToFMonsterG->Draw("hist same");
//hToFMonsterN->SetLineColor(4);
hToFMonsterN->Draw("hist");
hToFMonsterNcoinc->SetLineColor(2);
hToFMonsterNcoinc->Draw("hist same");
auto legend = new TLegend(.4,.55,.9,.9);
//legend->AddEntry(hToFMonster,"Monster ToF without selection","l");
//legend->AddEntry(hToFMonsterA,"Monster ToF withalpha selection","l");
//legend->AddEntry(hToFMonsterG,"Monster ToF with gamma selection","l");
legend->AddEntry(hToFMonsterN,"Monster ToF with neutron selection","l");
legend->AddEntry(hToFMonsterNcoinc,"Monster ToF with neutron selection and coinc in paris","l");
legend->Draw();


auto cToFMonsterParis = new TCanvas("ToF All Monster Paris ref","ToF All Monster Paris ref");
hToFMonsterNcoinc->Draw("hist");
hToFMonsterNParis->Draw("hist same");
auto legend2 = new TLegend(.6,.75,.9,.9);
legend2->AddEntry(hToFMonsterNcoinc,"Monster ToF with neutron selection and coinc in paris","l");
legend2->AddEntry(hToFMonsterNParis,"Monster ToF with neutron selection and paris as ref","l");
legend2->Draw();

auto cdiag = new TCanvas("hdiag","hdiag");
hdiag->Draw("hist");

auto c3 = new TCanvas("ToFMonster","ToFMonster");
c3->Divide(3,2);
for(int i=0;i<6;i++){
  c3->cd(i+1);
  ToFmonsterN[i]->Draw("hist");
  ToFmonsterG[i]->SetLineColor(2);
  ToFmonsterG[i]->Draw("hist same");
}

auto c4 = new TCanvas("EMonster","EMonster");
c4->Divide(3,2);
for(int i=0;i<6;i++){
  c4->cd(i+1);
  Emonster[i]->Draw("hist");
}

auto c5 = new TCanvas("EgammavsEstar","EgammavsEstar");
TF1 *diagonal = new TF1("line","[0]*x",0,12000);
diagonal->SetParameter(0,1);
EgammaEstar->Draw("colz");
diagonal->Draw("same");

auto c6 = new TCanvas("EgammavsToF","EgammavsToF");
EgammaToF->Draw("colz");


/*
Emonster[0]->SetLineColor(1);
for(int i=1;i<6;i++){
Emonster[i]->SetLineColor(i+1);
Emonster[i]->Draw("hist same");
}*/


auto c8 = new TCanvas("MonsterPSDvsToF","MonsterPSDvsToF");
MonsterPSDToF[0]->Draw("colz");
auto l3 = new TLine(38,PSDMonster[0],38,0.6);
l3->SetLineColor(2);
l3->SetLineWidth(2);
l3->Draw("same");
auto l4 = new TLine(38,PSDMonster[0],200,PSDMonster[0]);
l4->SetLineColor(2);
l4->SetLineWidth(2);
l4->Draw("same");
/*
c8->Divide(3,2);
for(int i=0;i<6;i++){
c8->cd(i+1);
MonsterPSDToF[i]->Draw("colz");
}
*/

auto c9 = new TCanvas("MonsterPSD","MonsterPSD");
MonsterPSD[0]->Draw("colz");
/*
c9->Divide(3,2);
for(int i=0;i<6;i++){
c9->cd(i+1);
MonsterPSD[i]->Draw("colz");
}
*/
auto c21 = new TCanvas("ParisPSD","ParisPSD");
ParisPSD[0]->Draw("colz");

/*
auto c10 = new TCanvas("MonsterPSDvsToF alpha","MonsterPSDvsToF alpha");
c10->Divide(3,2);
for(int i=0;i<6;i++){
c10->cd(i+1);
MonsterPSDToFAlpha[i]->Draw("colz");
}
auto c11 = new TCanvas("MonsterPSDvsToF neutron","MonsterPSDvsToF neutron");
c11->Divide(3,2);
for(int i=0;i<6;i++){
c11->cd(i+1);
MonsterPSDToFNeutron[i]->Draw("colz");
}
*/
auto c12 = new TCanvas("ToF Paris Cluster 1","ToF Paris Cluster 1");
c12->Divide(3,3);
for(int i=0;i<9;i++){
  c12->cd(i+1);
  ToFParis[i]->Draw("hist");
}

auto c13 = new TCanvas("ToF Paris Cluster 2","ToF Paris Cluster 2");
c13->Divide(3,3);
for(int i=0;i<9;i++){
  c13->cd(i+1);
  ToFParis[i+9]->Draw("hist");
}


/*

auto c16 = new TCanvas("Calib LaBr3 Cluster 1","Calib LaBr3 Cluster 1");
c16->Divide(3,3);
for(int i=0;i<9;i++){
c16->cd(i+1);
Calib_LaBr3[i]->Draw("hist");
}
auto c17 = new TCanvas("Calib LaBr3 Cluster 2","Calib LaBr3 Cluster 2");
c17->Divide(3,3);
for(int i=0;i<9;i++){
c17->cd(i+1);
Calib_LaBr3[i+9]->Draw("hist");
}

auto c18 = new TCanvas("Calib NaI Cluster 1","Calib NaI Cluster 1");
c18->Divide(3,3);
for(int i=0;i<9;i++){
c18->cd(i+1);
Calib_NaI[i]->Draw("hist");
}
auto c19 = new TCanvas("Calib NaI Cluster 2","Calib NaI Cluster 2");
c19->Divide(3,3);
for(int i=0;i<9;i++){
c19->cd(i+1);
Calib_NaI[i+9]->Draw("hist");
}
*/
auto c20 = new TCanvas("EgammavsToFgamma","EgammavsToFgamma");
EgammaToFgamma->Draw("colz");

auto c22 = new TCanvas("Paris Dt","Paris Dt");
hdt->Draw("hist");
//hdt->GetYaxis()->SetRangeUser(0,hdt->GetMaximum()*1.1);
cout << hdt->GetMaximum()*1.05 << endl;
auto l = new TLine(-time_window/1000.,0,-time_window/1000.,hdt->GetMaximum()*1.05);
l->SetLineColor(2);
l->SetLineWidth(2);
l->Draw("same");
auto l2 = new TLine(time_window/1000.,0,time_window/1000.,hdt->GetMaximum()*1.05);
l2->SetLineColor(2);
l2->SetLineWidth(2);
l2->Draw("same");

auto c23 = new TCanvas("Single Paris","Single Paris");
hadd2->SetLineColor(1);
hadd2->Draw("hist");
hadd1->SetLineColor(2);
hadd1->Draw("hist same");
hc1->SetLineColor(3);
hc1->Draw("hist same");
hc2->SetLineColor(4);
hc2->Draw("hist same");


c23->Update();
auto legend4 = new TLegend(.7,.78,.9,.9);
legend4->AddEntry(hc1,"All gammas in paris cluster 1 without add-back","l");
legend4->AddEntry(hc2,"All gammas in paris cluster 2 without add-back","l");
legend4->AddEntry(hadd1,"All gammas in paris cluster 1 with add-back","l");
legend4->AddEntry(hadd2,"All gammas in paris cluster 2 with add-back","l");
legend4->Draw();

/*
auto c24 = new TCanvas("AddBack Paris","AddBack Paris");
hadd1->Draw("hist");
hadd2->SetLineColor(3);
hadd2->Draw("hist same");


c24->Update();
auto legend5 = new TLegend(.7,.78,.9,.9);
legend5->AddEntry(hadd1,"All gammas in paris cluster 1 with add-back","l");
legend5->AddEntry(hadd2,"All gammas in paris cluster 2 with add-back","l");
legend5->Draw();


auto c25 = new TCanvas("Cluster 1 Paris","Cluster 1 Paris");
hc1->Draw("hist");
hadd1->SetLineColor(3);
hadd1->Draw("hist same");


c25->Update();
auto legend6 = new TLegend(.7,.78,.9,.9);
legend6->AddEntry(c1,"All gammas in paris cluster 1 without add-back","l");
legend6->AddEntry(hadd1,"All gammas in paris cluster 1 with add-back","l");
legend6->Draw();


auto c26 = new TCanvas("Cluster 2 Paris","Cluster 2 Paris");
hc2->Draw("hist");
hadd2->SetLineColor(3);
hadd2->Draw("hist same");


c26->Update();
auto legend7 = new TLegend(.7,.78,.9,.9);
legend7->AddEntry(c2,"All gammas in paris cluster 2 without add-back","l");
legend7->AddEntry(hadd2,"All gammas in paris cluster 2 with add-back","l");
legend7->Draw();
*/


// Save all histogram if an out file was given
if(outfname!=""){
  TFile * fout = new TFile(outfname.c_str(), "RECREATE");
  labels->Write();
  hg->Write();
  hadd->Write();
  hsel->Write();
  hdiag->Write();
  hToFParis->Write();
  hToFMonsterN->Write();
  hToFMonsterNParis->Write();
  hToFMonsterNcoinc->Write();
  hToFMonsterG->Write();
  hToFMonsterA->Write();
  hToFMonster->Write();
  EgammaEstar->Write();
  ToFgammaEstar->Write();
  ToFgammaToFneutron->Write();
  EgammaToF->Write();
  EgammaToFgamma->Write();
  hdt->Write();

  for(int i=0;i<18;i++){
    ToFParis[i]->Write();
    ParisPSD[i]->Write();
  }

  for(int i=0;i<6;i++){
    ToFmonsterN[i]->Write();
    ToFmonsterG[i]->Write();
    ToFmonsterAlpha[i]->Write();
    Emonster[i]->Write();
    MonsterPSD[i]->Write();
    MonsterPSDToF[i]->Write();
    MonsterPSDToFAlpha[i]->Write();
    MonsterPSDToFNeutron[i]->Write();
  }
  fout->Close();
}

cout << "Number of tref at 0 : " << ntref0 << endl;
cout << "Number of non 0 tref : " << ntref << endl;
cout << "Charge : " << charge << " µC" << endl;
}
