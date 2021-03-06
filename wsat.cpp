#include "wsat.h"
#include "history.h"
#include <cstring>
#include <time.h>
#include <sys/times.h> 
#include <unistd.h>
#include <sys/types.h>
#include <fcntl.h>
#include<stdlib.h>
#include <vector>


struct 	tms start, stop;
double usedtime = 0;

#define oops(msg) {perror(msg); exit(1);}
#define MAXEXESEC 5000
vector<string> split(const string& str, const string& delim)
 { 
	vector<string> res; 
        if("" == str) return res; //先将要切割的字符串从string类型转换为char*类型 
        char * strs = new char[str.length() + 1] ; //不要忘了 
        strcpy(strs, str.c_str());
        char * d = new char[delim.length() + 1];
        strcpy(d, delim.c_str());
        char *p = strtok(strs, d);
        while(p) { string s = p; //分割得到的字符串转换为string类型
        res.push_back(s); //存入结果数组
         p = strtok(NULL, d); 
          }
   return res; 
}

int cpick_skc()
{
	int		k,c,v,ci;
	int 	bestvar_array[1000];
	int		bestvar_count;
	int		best_bbreak;
	int		bbreakv;
	int		*truep;
	
	double r;
	/*直接从不满足子句中随机选择*/
	c = unsat_stack[rand()%unsat_stack_fill_pointer];
	
	//the first var
	v = clause_lit_h[c][0].var_num;//获得一个变元
	truep = (cur_soln[v])? var_poslit_h[v]:var_neglit_h[v];//获得当前变元赋值的所有的子句集
	
	bbreakv=0;
	for(; (ci=*truep)!=-1; ++truep)
	{
		if (sat_count[ci]==1) ++bbreakv;
	}
	
	best_bbreak = bbreakv;//如果翻转多少变元会被干掉
	bestvar_array[0] = v;
	bestvar_count = 1;	
	
	//the remaining vars
	for(k = 1; k < clause_lit_count_h[c]; ++k)
	{
		v = clause_lit_h[c][k].var_num;
		truep = (cur_soln[v])? var_poslit_h[v]:var_neglit_h[v];
		bbreakv=0;
		for(; (ci=*truep)!=-1; ++truep)
		{
			if (sat_count[ci]==1) 
			{
				if (bbreakv == best_bbreak) break;
				++bbreakv;					
			}
		}
		
		if(ci != -1) continue;//implies bbreakv>best_bbreak
		
		if (bbreakv < best_bbreak)
		{
			best_bbreak = bbreakv;
			bestvar_array[0] = v;
			bestvar_count = 1;
		}
		else// if (bbreakv == best_bbreak)
		{
			bestvar_array[bestvar_count]=v;
			++bestvar_count;
		}
	}
	/*************************
	上诉有两个问题
	1. 存在后来抹去前面变元的问题
	2. 选择过于贪心
	3. 潜在破坏
	*************************/
	if(best_bbreak == 0) return bestvar_array[rand()%bestvar_count];//此处有改进方案？？？？最近最少翻转？？？
    /*  byMy
	要不要颠覆损失？？？？
	*/
	r = (rand()%MY_RAND_MAX_INT)*BASIC_SCALE;
	
	if(r > wp)
	{
		if(bestvar_count == 1) return bestvar_array[0];//永远选最少破坏的子句
		else return pick_bestvar(bestvar_array, bestvar_count);
		//return bestvar_array[rand()%bestvar_count];
	}
	else
	{
		return pick_inference(c);
		//return clause_lit[c][rand()%clause_lit_count[c]].var_num;
	}
}


int (*pick) ();

/*void set_fun_par()
{
	//set wp
	if(max_clause_len <= 3) 
	{
		flip = flip_simp;
		pick = cpick_skc;
		if(ratio<=4.22) wp = 0.567;
		else if(ratio<=4.23) wp = 0.567-(ratio-4.2)/20;
		else if (ratio<4.26) wp = 0.561-(ratio-4.252)*7/30;
		else wp = 0.554-(ratio-4.267)*2/5;
		
		cout<<"c Algorithmic: WalkSAT"<<endl;
		cout<<"c Algorithmic: Noise = "<<wp<<endl;
	}
}*/


void local_search(int max_flips)
{
	min_unsat = num_clauses_h;
	int nobetter_steps = 0;
	#include <vector>
	for (step = 0; step < max_flips; step++)
	{
		times(&stop);
		usedtime = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
		if(unsat_stack_fill_pointer == 0 || usedtime >= (double)MAXEXESEC) return;
		flipvar = cpick_skc();
		save_when_flip();
		flip_simp(flipvar);
		if(min_unsat > unsat_stack_fill_pointer)
		{
			min_unsat = unsat_stack_fill_pointer;
			nobetter_steps = 0;
		}
		else
		{
			nobetter_steps++;
			if(nobetter_steps == 1000)
			{
				//????
				//cout<<"min_unsat:"<<step<<"("<<min_unsat<<")"<<endl;
			}
		}
	}
}

void creat_logfile(char *filename, char *instance, char *dirname, char *satname)
{
	char tmp[512];
	int i;
	for(i = 0; i < strlen(instance); i++)
	{
		if(instance[i] == '/') tmp[i] = '-';
		else tmp[i] = instance[i];
	}
	tmp[i] = '\0';
	strcpy(filename, dirname);
	strcat(filename, satname);
	strcat(filename, tmp);
	cout << "creat logfile success" << endl;
}
void copyFile(char *namesource,const char *namecopy)
{
   
  int in,out,flag; 
  char buffer[1024]; 
  in = open(namesource,O_RDWR|O_CREAT);
  out = open(namecopy,O_RDWR|O_CREAT);
  while((flag=read(in,buffer,1024))>0) 
{  write(out,buffer,flag); } 
 close(in); 
 close(out); 

 


}

string resultdir="./result/";
positive_signratio *Out;
int run_cnf(int argc, char* argv[])
{
	int seed, tries; 
	int	satisfy_flag = 0;
	char instance[512];
	strcpy(instance, argv[1]);
	char filename[512];
	char dirname[128] = "../../result/";
	char satname[128] = "isat3"; 
	if (build_instance_h(argv[1]) == 0 ) {
		cout << "build_instance_h failed" << endl;
		return -1;
	}/*history.h*/

	sscanf(argv[2],"%d",&seed);
    sscanf(argv[3],"%lf",&wp);
	times(&start);
	srand(seed);
	//set_fun_par();
	Out=new positive_signratio[num_vars_h];
	cout<<endl;
	srand((unsigned int)(time(NULL)));//！！！？？？？？？？？？？？？？？？？？？？？？？？？？？？
	
	for (tries = 0; tries < max_tries; tries++) 
	{
		init();
		local_search(max_flips);
		if (unsat_stack_fill_pointer == 0) 
		{
			if(verify_sol()==1) {satisfy_flag = 1; break;}
			else {
				   cout<<"Sorry, something is wrong."<<endl;
			}
		}
		if(usedtime >= (double)MAXEXESEC) break;
	}

	if(satisfy_flag==1)
	{
	  print_solution(Out);
	}
	else  cout<<"s UNKNOWN"<<endl;
	times(&stop);
	double comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
	cout<<"c solveSteps = "<<tries<<" tries + "<<step<<" steps (each try has "<<max_flips<<" steps)."<<endl;	
	
    //system("clear");
    vector<string>res=split(argv[1],"/");
    return 0;
}



int main(int argc, char **argv)
{
	run_cnf(argc, argv);
}
