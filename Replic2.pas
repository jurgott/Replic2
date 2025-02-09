{ $ R + }
program Replic2;
{
 Replicate numbers of SNPs in array 1 with SNPs in array 2.
 Arrays need not be the same length. For an observed number
 m of matches, determine random probability (p-value) of
 finding m or more matches.
 04 Feb 2025 written
 05 Feb 2025 streamlined
 06 Feb 2025 input file name on command line
}
uses sysutils;
label 44;

type
 integer=longint; real=double;

const
 version = '06 Feb 2025';
 maxSNP=180000;
 maxbestSNPs=10000;
 maxmergedSNPs = 2*maxbestSNPs;
 maxrepl=100000;
 k10=10000;

type
 vector=array[1..maxSNP] of integer;
 vect = array[1..maxmergedSNPs] of integer;

var
 numlargeSNPs,numbestSNPs:array[1..2] of integer;
 ii,mal,Nrepli,irepli,Nmatch,Nmatch0,Ntot,pval,errno:integer;
 u,v,w:QWord;
 seed:QWord; {Called j in Press book}
 largeSNPs:vector;
 mergedSNPs:vect;
 infile,outfile:text;
 infilename,outfilename:string;
 answer:boolean;


procedure hpsort(n:integer; var ra:vect);
{
 Sorts an array ra(1:n) into ascending numerical
 order using the Heapsort algorithm. n is input;
 ra (real ==> integer) is replaced on output by its sorted
 rearrangement. Based on Press et al, "Numerical
 Recipes in F77", 1992, p. 329

 On return, the smallest number will be ra[1],
 the largest ra[n]; values in increasing order.
}

label 10,20,95;
var
 i,ir,j,L:integer;
 rra:integer;

begin {hpsort}
 if n<2 then goto 95;
 L := 1 + (n div 2);
 ir := n;

 10:
 if (L>1) then begin
 {L:=L-1;}
  dec(L);
  rra:=ra[L];
 end else begin
  rra:=ra[ir];
  ra[ir]:=ra[1];
 {ir:=ir-1;}
  dec(ir);
  if (ir=1) then begin
   ra[1]:=rra;
   goto 95;
  end;
 end;
 i:=L;
 j:=L+L;

 20:
 if (j <= ir) then begin
  if (j<ir) then begin
   if (ra[j]<ra[j+1]) then inc(j);
  end;
  if (rra<ra[j]) then begin
   ra[i]:=ra[j];
   i:=j;
   j:=j+j;
  end else j:=ir+1;
  goto 20;
 end; {if}

 ra[i]:=rra;
 goto 10;
 95:
end; {hpsort}


procedure init;
begin
 writeln('Program Replic2 version ',version);
 writeln('Jurg Ott, Rockefeller University, New York');
 writeln;
 writeln('Run Replic2 by answering questions or by naming an input file');
 writeln('on the command line. Sample input lines of such a file:');
 writeln('  179100 179800   Two numbers of overall SNPs');
 writeln('   10000  10000   Two numbers of best SNPs');
 writeln('         100000   Number of random replicates');
 writeln('            600   Number of matches -- repeat as often as desired');
 writeln('             -1   To terminate this run');
 writeln;
 writeln('Current maximum program constants:');
 writeln(maxSNP:10,' overall variants in either group');
 writeln(maxbestSNPs:10,' selected best variants in either group');
 writeln(maxmergedSNPs:10,' variants merged from the two sets of best variants');
 writeln(maxrepl:10,' random replicates for p-value calculation');
 writeln;
 answer := (paramcount=0); {if false ==> file name on command line}

 if not answer then begin {Read from file}
  infilename:=paramstr(1);
  if not FileExists(infilename) then begin
   writeln(infilename,' file not found');
   halt;
  end; {if}
  assign(infile,infilename); reset(infile);
  outfilename := 'R2-'+infilename+'.out';
 end {if not answer}

 else outfilename := 'Replic2.out'; {Answer questions}

 assign(outfile,outfilename); rewrite(outfile);
 errno:=0;
end; {init}



 FUNCTION iint64():QWord;
 {
  This function returns a 64 bit integer random number when the
  values of u,v,w have already been set by the raninit procedure.
  Repeatedly calling this function will get many random numbers.

  Based on Press WH, Teukolsky SA, Vetterling WT, Flannery BP (2007)
  "Numerical recipes 3rd edition: The art of scientific computing."
  Cambridge University Press, Cambridge, UK; New York
 }
 CONST
  LL28: qword = 2862933555777941757;
  LL70: qword = 7046029254386353087;
  U42: longword = 4294957665;
 VAR x: QWord;
 BEGIN {iint64}
  u := u * LL28 + LL70;
  v := v xor (v shr 17); v := v xor (v shl 31); v := v xor (v shr 8);
  { $ffffffff = %11111111111111111111111111111111 is hexadecimal/binary for 4294967295 }
  w := U42 * (w and $ffffffff) + (w shr 32);
  x := u xor (u shl 21);  x := x xor (x shr 35);  x := x xor (x shl 4);
  iint64 := (x + v) xor w;
 END; {iint64}



 FUNCTION doub():double;
 {
  This function returns a double precision floating random
  number in the range 0 to 1 when the values of u,v,w have
  already been set by the raninit procedure. Repeatedly
  calling this function will get many random numbers.
 }
 CONST rr: double = 5.42101086242752217E-20;
 BEGIN {doub}
  doub := rr * iint64;
 END; {doub}



 PROCEDURE raninit;
 {
  This function initiates the random number generator, iint64, that is,
  it sets the states of global variables u,v,w, given a seed j ("seed").
  Note: int64 is a predefined number type in Pascal; need to name desired
  function iint64 instead. Generator has a period of 3.138 x 10^57.

  Based on Press WH, Teukolsky SA, Vetterling WT, Flannery BP (2007)
  "Numerical recipes 3rd edition: The art of scientific computing."
  Cambridge University Press, Cambridge, UK; New York

  Required global declarations:
 VAR
  u,v,w:QWord;
  seed:QWord; Called j in Press book.
 }

 CONST LL41: qword = 4101842887655102017;

 VAR
  ok:boolean;
  res:longword;
  seedlimit:int64;

 BEGIN {raninit}

  {Generate random number}
  seedlimit:=9223372036854775806;
  seed := random(seedlimit);
  if (seed=LL41) then begin
   writeln('ERROR: The seed must not be equal to the following number:');
   writeln(' ',LL41);
   halt;
  end;

  {Check proper sizes of numbers}
  ok := (sizeof(res)=4) and (sizeof(seed)=8);
  if not ok then begin
   writeln('ERROR: One or both of the following number sizes are incorrect:');
   writeln(' longword = 4, qword = 8. Random number generator must be updated.');
   halt;
  end;

  v := LL41;
  w := 1;
  u := seed xor v; iint64;
  v := u; iint64;
  w := v; iint64;
 END; {raninit}



 procedure ranper(var aa:vector; mm:integer); {aa is integer}
{Manly book, 2007; refers to Knut's algorithm P. This is good}
 var
  jj,kk:integer;
  hold:integer; {same type as aa}
 begin
  jj:=mm;
  repeat
   {Random integer between 1 and jj}
   kk:=trunc( jj*doub ) + 1;
   if kk<1 then kk:=1 else if kk>jj then kk:=jj;
   {Exchange aa[jj] and aa[kk]}
   hold:=aa[jj]; aa[jj]:=aa[kk]; aa[kk]:=hold;
   jj:=jj-1;
  until jj=1;
 end;



begin {Replic2}
 init;

 {Parameters}
 if answer then begin
  writeln('Enter 2 numbers of overall SNPs');
  for ii:=1 to 2 do read(numlargeSNPs[ii]); readln;

  writeln('Enter 2 numbers of best SNPs (they are usually equal to each other)');
  for ii:=1 to 2 do begin
   read(numbestSNPs[ii]);
   if numbestSNPs[ii] >= numlargeSNPs[ii] then begin
    writeln('Number of best SNPs >= overall number of SNPs');
    halt;
   end;
  end; {for ii}
  readln;

  writeln('Enter number of random replicates');
  readln(Nrepli);

 end else begin {not answer, read from infile}
  for ii:=1 to 2 do read(infile,numlargeSNPs[ii]); readln(infile);

  for ii:=1 to 2 do begin
   read(infile,numbestSNPs[ii]);
   if numbestSNPs[ii] >= numlargeSNPs[ii] then begin
    writeln('Number of best SNPs >= overall number of SNPs');
    halt;
   end;
  end; {for ii}
  readln(infile);

  readln(infile,Nrepli);
 end; {else begin}

 {Check limits}
 for ii:=1 to 2 do begin
  if numlargeSNPs[ii]>maxSNP then inc(errno);
  if numbestSNPs[ii]>maxbestSNPs then inc(errno);
 end; {for}
 if Nrepli>maxrepl then inc(errno);
 if errno>0 then begin
  writeln(' ',errno,' parameters exceed limits of program constants');
  halt;
 end;

 {Initialize random number generator and long list}
 writeln('Program Replic2 version ',version);
 raninit;
 for ii:=1 to maxSNP do largeSNPs[ii]:=ii;

 {Output}
 writeln(outfile,numlargeSNPs[1],' ',numlargeSNPs[2],'  Two overall numbers of SNPs');
 writeln(outfile,numbestSNPs[1],' ',numbestSNPs[2],'  Two numbers of best SNPs');
 writeln(outfile,Nrepli,'  Random replicates');
 writeln(outfile);
 writeln(outfile,'matches p-value');

 if answer then begin
  writeln('Enter observed number of matches, as many lines as needed.');
  writeln('To stop, enter -1');
 end;

 44:
 if answer then begin
  if eof(input) then Nmatch:=-1 else readln(Nmatch);
 end else begin {read from file}
  if eof(infile) then Nmatch:=-1 else readln(infile,Nmatch);
  if Nmatch>0 then writeln('Doing ',Nmatch,' matches');
 end; {else begin}

 if Nmatch<0 then begin
  writeln('All done. File "',outfilename,'" written');
  close(outfile);
  halt;
 end;

 pval:=0;

 {Do replicates}
 for irepli:=1 to Nrepli do begin
  Ntot:=0;
  if (irepli mod k10)=0 then writeln(' ',(irepli div k10),'K of ',(Nrepli div k10),'K');

  for mal:=1 to 2 do begin
   {Scramble/permute large array}
   ranper(largeSNPs,numlargeSNPs[mal]); 
   {Copy "top" numbestSNPs[mal] SNP IDs (numbers) to mergedSNPs}
   for ii:=1 to numbestSNPs[mal] do begin
    inc(Ntot);
    mergedSNPs[Ntot]:=largeSNPs[ii];
   end; {for ii}
  end; {for mal}

  {Sort mergedSNPs array so matches can be counted}
  hpsort(Ntot,mergedSNPs);
  Nmatch0:=0;
  for ii:=2 to Ntot do
  if mergedSNPs[ii]=mergedSNPs[ii-1] then inc(Nmatch0);

  if Nmatch0 >= Nmatch then inc(pval);
 end; {for irepli}

 {Result}
 writeln(Nmatch,'  p-value = (',
  pval,'+1)/(',Nrepli,'+1) = ',( (pval+1)/(Nrepli+1) ):10:8);
 writeln(outfile,Nmatch,' ',( (pval+1)/(Nrepli+1) ):10:8);
 goto 44;
end. {Replic2}
