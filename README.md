# Cause Consequence Diagrams (CCD)

CCD HOL Theorems and mathematical formulations are currently supported for Linux users only

"-----------------------------------------  Installing HOL in Linux ---------------------------------------------------"

1- Make sure that the GCC compiler is properly installed, if not then open the terminal and use the following command.
sudo apt-get update
sudo apt-get install build-essential

2- Download the PolyML 5.7 
(Download Link: https://osdn.net/frs/g_redir.php?m=kent&f=polyml%2Fpolyml%2F5.7%2Fpolyml-5.7.tar.gz). 
Untar the package into any directory of your choice.

3- Open the terminal and enter into the package directory using cd command. e.g.
Abdelghany@ubuntu:~ cd /Downloads/polyml-5.7$

4- In the PolyML directory, type the following commands one by one;
./configure --prefix=/usr
make
sudo make install

5- The latest HOL-kananankis-12 (HOL4) can be download from GitHub (https://github.com/HOL-Theorem-Prover/HOL)
Once the download finished and enter into the HOL package directory using cd command. e.g.
Abdelghany@ubuntu:~/Downloads/HOL$

6- Type the following command in terminal,
poly < tools/smart-configure.sml

Wait for configuration to complete!

7- Type the following command in terminal,
bin/build

The installation of HOL begins if the above procedure is followed correctly, and after some time, it will complete the installation.

8- Install the Emacs by using the following command in the terminal.
sudo apt-get install emacs

After completion of Emacs installation, open emacs, and load the file “hol-mode.el” from HOL directory. e.g.

a) At Emacs, Press ALT-x and type “load-file” then press enter
b) A cursor appears at the bottom, type the path “~/Downloads/HOL/tools/hol-mode.el” then press enter
c) Press ALT-h 3 (it will split the Emacs screen into two columns and the HOL shell is running on the right screen)
d) The tab “HOL”, at the top of Emacs bar, contains several shortcuts to interact with HOL shell.

A more detail description of the Emacs HOL commands can be found in https://hol-theorem-prover.org/hol-mode.html.


"-----------------------------------------  Installing CCD Code ----------------------------------------------"

To use the CCD theorems and mathematical formulations, load all the necessary files (sequentially one by one) 
in the HOL shell as follows: 

The tab “HOL”, at the top of Emacs bar ==> Misc ==> Load file 
==> ETree.sml ==> RBD.sml ==> FT_deep.sml ==> CCD.sml    

Now all CCD formulations are proved in the HOL shell and ready to be used!

"--------------------------------------------  CCD Theorems  -------------------------------------------------"

All theorems are stored under a specific different name as follows: store_thm("name")"

Entre the name of any theorem exist at the file "CCD.sml", for instance, "FOUR_DECISION_BOXES_1002" 
in the HOL shell, the HOL will load this theorem directly for use without reproof it again.         

"--------------------------- IEEE 39-Bus Power System Application  -------------------------------------------"

We applied our CCD theorems on a real-world application IEEE 39-Bus Power System to show the capability of 
the CCD formulations to obtain a component-level reliability/failure expression easily.  

To load the file ==> press the tab “HOL" ==> Misc ==> Load file ==> IEEE_39_BUS_POWER_SYSTEM.sml

"----------------------------------------   Contacts ---------------------------------------------------------"

Mohamed Abdelghany  (m_eldes@ece.concordia.ca)

Prof. Sofiene Tahar (tahar@ece.concordia.ca)
