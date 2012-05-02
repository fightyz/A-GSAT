/*********************************************************/
/*  GSAT - Greedy Local Search Satisfiability Procedure  */
/*                                                       */
/*  Bart Selman and Henry Kautz                          */
/*                                                       */
/*                                                       */
/*  For information about this program, contact          */
/*      selman@cs.cornell.edu                            */
/*      kautz@cs.washington.edu                          */
/*********************************************************/

#include "gsat.h"
#include "anneal.h"
#include "utils.h"
#include "adjust_bucket.h"
#include <sys/times.h>

#ifdef SYSVR4
#include <sys/times.h>
#include <limits.h>
#define NO_USLEEP
#endif

#ifdef XGSAT
#include "xgsat.h"
#endif

/************************/
/* Forward Declarations */
/************************/

EXTERN_FUNCTION (void flip_var, (int var));
EXTERN_FUNCTION (void propagate_from, (int var));
EXTERN_FUNCTION (void main_wrapup, (char * msg));


/**************************/
/*  Parsing Parameters    */
/**************************/

void
parse_parameters()
{
    char inputline[MAXLINE];
    float f;
    char word1[MAXLINE];
    char word2[MAXLINE];
    int option;
    int i;

    strcpy(assign_file, "/dev/null");//globals.c里定义：char assign_file[MAXLINE]，gsat.h里extern
    strcpy(report_file, "/dev/null");

//globals.c里定义char program_name[] = PROGRAM_NAME ;gsat.h里extern，且#define PROGRAM_NAME "program: gsat version 42, June 2002\n"
    printf(program_name);
#ifdef SYSVR4
    uname(&hostutsname);
    printf("host: %s\n", hostutsname.nodename);
    strncpy(hostname, hostutsname.nodename, MAXLINE);
#else
    gethostname(hostname, MAXLINE);//获得主机名，在globals.c里，char hostname[MAXLINE] = "unknown";
    printf("host: %s\n", hostname);
//uname是linux的系统调用，int uname(struct utsname * buf)，hostutsname在gsat.h里extern struct utsname hostutsname;一些系统信息
    uname(&hostutsname);
#endif
    printf("machine: %s\n", hostutsname.machine);//当前硬件体系类型

//globals.c和gsat.h里，long int raw_start_time current time of day;time(NULL)将返回自1970年1月1日0点走过的秒数，存在raw_start_time中（raw未处理）
    raw_start_time = time(NULL);
    raw_start_tmptr = localtime(&raw_start_time);//将总秒数变成规则的时间
    sprintf(datestring, "%02d/%02d/%02d  %02d:%02d:%02d",
	    raw_start_tmptr->tm_year,
	    raw_start_tmptr->tm_mon + 1,
	    raw_start_tmptr->tm_mday,
	    raw_start_tmptr->tm_hour,
	    raw_start_tmptr->tm_min,
	    raw_start_tmptr->tm_sec);

    printf("date: %s\n", datestring);

    /* Read file names */
//get_input_file_name在utils.c里。wff_file的值从函数实现的gets(name)中来，gets会读入stdin，因此你要输入wff_file的文件名
    get_input_file_name("wff_file: ", wff_file);
    printf("wff_file: %s\n", wff_file);
    get_symbol("assign file (default = /dev/null): ", assign_file);//从stdin获取assign file(做什么的？)的路径和文件名，输a则是在当前目录下建一个a文件
    printf("assign_file: %s\n", assign_file);

    sprintf(report_file, "rep.%s.%02d%02d%02d.%02d%02d%02d",
	    wff_file,
	    raw_start_tmptr->tm_year,
	    raw_start_tmptr->tm_mon + 1,
	    raw_start_tmptr->tm_mday,
	    raw_start_tmptr->tm_hour,
	    raw_start_tmptr->tm_min,
	    raw_start_tmptr->tm_sec);

    printf("report file (default = %s): ", report_file);
    get_symbol("", report_file);
    printf("report_file: %s\n", report_file);
  
    /* Read number flips, tries, and reset steps */
    while (1) {
	printf("max flips (default = # vars x 5; enter N or xN): ");
	fgets(inputline, MAXLINE, stdin);

	if (1==sscanf(inputline, " %d", &max_flips)) break;//max_flips是整数
	if (1==sscanf(inputline, " x%d", &max_flips)) {//max_flips是负数
	    max_flips *= -1; break; }
	if (empty_string(inputline)){
	    max_flips = -5; break; }//如果直接回车max_flips就是-5
	crash_maybe("Error: bad input\n");
    }
    if (max_flips >= 0) //max_flips是整数，意思是用户输入了自定义的flips数
      printf("max_flips: %d\n", max_flips);
    else
      printf("max_flips: %d x num_vars\n", -max_flips);//max_flips是负数意思是flips数是变量数的-max_flips倍,用户未自定义则max_flips=-5
    while (1) {
	printf("max tries (default = 1): ");
	fgets(inputline, MAXLINE, stdin);
	if (1==sscanf(inputline, " %d", &max_tries)) break;
	if (empty_string(inputline)){
	    max_tries = 1; break; }
	crash_maybe("Error: bad input\n");
    }
    printf("max_tries: %d\n", max_tries);
//以下各种变量参考globals.c，大多有注释，很多是basic gsat用不到的
    report_interval = 1000;
    flag_superlinear = 0;
    flag_hillclimb = 0;
    flag_format = 0;
    flag_mail = 0;
    flag_plateau = 0;
    flag_hole = 0;
    flag_hole_continue = 0;
    flips_to_plateau = 0;
    flag_direction = 0;
    flag_save_best_max = SAVE_BEST_MAX_DEFAULT;
    flag_init_prop = 0;
    flag_multiple_assigns = 0;
    flag_fixed_init = 0;
    flag_convert = 0;
    flag_graphics = 0;
    flag_long_report = 0;
    flag_weigh_clauses = 0;
    flag_coloring = 0;
    flag_trace = FLAG_TRACE_TRIES;
    flag_walk = 0;
    flag_walk_all_vars = 0;
    flag_anneal = 0;
    flag_adaptive = 0;
    flag_only_unsat = 0;
    reset_weight_tries = 1;
    weight_update_amt = 1;
    reset_tries = 1;
    boost_threshhold = 0;
    boost_amount = 0;
    tabu_list_length = 0;
    odds_true = INT_PROB_BASE / 2;
    flag_manual_pick = 0;
    flag_bigflip = 0;
    seed1 = 0;
    seed2 = 0;
    rand_method = 1;
    one_bit_mask = DEFAULT_ONE_BIT_MASK;
    pause_usecs = 0;
    flag_partial = 0;
    init_file[0] = 0;

    /* Get and print optional parameters */
    while (1) {
	printf("option (? for help): ");


//直接回车什么都不输就是最基本的GSAT，一直到此函数完都是选项
	if (fgets(inputline, MAXLINE, stdin)==NULL) break;
	if (sscanf(inputline, " %s", word1)!=1) break;

	if (strcmp(word1,"?")==0) {
	    printf("  adaptive [N] = adaptive initialization with N mutations;\n");
	    printf("                 use N = -1 (not zero!) for no mutations\n");
	    printf("  anneal [FILE] = read annealing schedule from FILE, or stdin if no file\n");
	    printf("  b N M = boost at threshhold N for M more flips\n");
	    printf("  best N = save best & low assigns that score <= N;\n");
	    printf("           use N = 0 to only consider LAST assign of each try\n");
	    printf("  bigflip = flip all vars in unsatisfied clauses\n");
	    printf("  bucket = same as hillclimb option below\n");
	    printf("  c FILE = convert input wff and save as FILE\n");
	    printf("  color K = assume implicit clauses for a K-coloring\n");
	    printf("  d = downward moves only\n");
	    printf("  f = input wff MUST be f-format, error otherwise\n");
	    printf("  fix = use fixed random initialization for each random reset\n");
	    printf("  hillclimb = perform hillclimbing rather than pure greedy search\n");
	    printf("  init FILE = initialize with FILE; unspecified lits init to FALSE, unless partial option\n");
	    printf("  kf = input wff MUST be kf-format, error otherwise\n");
	    printf("  long = print long report\n");
	    printf("  m = find multiple assigns\n");
	    printf("  mail = send email with error messages\n");
	    printf("  mask N = use N as mask on random values for 0/1 flips\n");
	    printf("  only_unsat = greedy flips only choose among vars from unsat clauses\n");
	    printf("  partial = randomly assign vars not included in init file\n");
	    printf("  positive F = probability that var inits to true is F (default 0.5)\n");
	    printf("  plateau N = explore plateau with N unsat clauses by choosing sideways moves only\n");
	    printf("  hole [continue] = stop after finding first downward move from plateau\n");
	    printf("      keyword 'continue' means reset number of flips and continue plateau search\n");
	    printf("  p = init with unit propagation\n");
	    printf("  pause M = pause M seconds between flips (may be a decimal number)\n");
	    printf("  r N = random reset after N tries (default = 1)\n");
	    printf("  rand N = use random method number N (default = 1)\n");
	    printf("  report N = print report after every N tries (default = 1000)\n");
	    printf("  s = sideways and downwards moves only\n");
	    printf("  super = superlinear schedule of max-flips\n");
	    printf("  tabu N = use tabu list of length N\n");
	    printf("  seed N [M] = use N (and optionally M) as the random seed\n");
	    printf("  trace FLAG = trace also: 1=flips + 2=flip_clauses + 4=diffs + 8=makes +\n");
	    printf("               16=walks + 32=anneal + 64=clauses + 128=tries + 256=best +\n");
	    printf("               512=tabu + 1024=orphans + 2048=assign + 4096=clause_state\n");
	    printf("        (default is tries = 128;)\n");
	    printf("  silent = reset trace to 0 (no tracing)\n");
	    printf("  walk [all] F = random walk with probability F when max_diff<=0\n");
	    printf("      F < 0 means random walk even when max_diff>0\n");
	    printf("      keyword 'all' means randomly pick from all variables,\n");
	    printf("      otherwise only pick variables with postive make\n");
	    printf("  weight [N] [M] = use clause weights when selecting variable to flip\n");
	    printf("      resetting weights every N tries (default 1 means reset each assign)\n");
	    printf("      updating weights by M after each failure (default 1)\n");
	    printf("  xgsat = create graphical display (not for n-queens)\n");
	    printf("  xqueens FILE = use FILE to communicate with queens X graphics\n\n");}
	else if (strcmp(word1,"d")==0) {
	    printf(" option: downward moves only\n");
	    flag_direction = 1; }
	else if (strcmp(word1,"s")==0) {
	    printf(" option: downward and sidedways moves only\n");
	    flag_direction = 2; }
	else if (strcmp(word1,"p")==0) {
	    printf(" option: init with unit propagation\n");
	    flag_init_prop = 1; }
	else if (strcmp(word1,"super")==0) {
	    printf(" option: superlinear schedule of max-flips\n");
	    flag_superlinear = 1; }
	else if (strcmp(word1,"only_unsat")==0) {
	    printf(" option: only pick vars from unsat clauses\n");
	    flag_only_unsat = 1; }
	else if (sscanf(inputline, " walk %f", &f)==1 || 
		 sscanf(inputline, " walk all %f", &f)==1) {
	    flag_walk = (f * INT_PROB_BASE); 
	    printf(" option: random walk = %f\n", f);
	    if (f<0)
	      printf("         walk even when diff>0\n", f);
	    if (sscanf(inputline, " walk all %f", &f)==1){
		flag_walk_all_vars = 1;
		printf("         pick from all variables\n", f);
	    }
	}
	else if (strcmp(word1, "hole") == 0) {
	    flag_hole = 1;
	    printf(" option: find first hole on plateau\n");
	    if ((sscanf(inputline, " %s %s", word1, word2) == 2) && (strcmp(word2, "continue") == 0)) {
		flag_hole_continue = 1;
		printf("         continue searching plateau\n");
	    }
	}
	else if (strcmp(word1,"m")==0) {
	    printf(" option: find multiple assignments \n");
	    flag_multiple_assigns = 1; }
	else if (strcmp(word1,"manual")==0) {
	    printf(" option: manual picks\n");
	    flag_manual_pick = 1; }
	else if (strcmp(word1,"mail")==0) {
	    printf(" option: email error messages\n");
	    flag_mail = 1; }
	else if (strcmp(word1,"np")==0 || strcmp(word1,"f")==0) {
	    printf(" option: f-format \n");
	    flag_format = FLAG_FORMAT_F; }
	else if (strcmp(word1,"kf")==0) {
	    printf(" option: kf-format \n");
	    flag_format = FLAG_FORMAT_KF; }
	else if (strcmp(word1,"fix")==0) {
	    printf(" option: fixed random initialized\n");
	    flag_fixed_init = 1; }
	else if (strcmp(word1,"hillclimb")==0) {
	    printf(" option: hillclimb\n");
	    flag_hillclimb = 1; }
	else if (strcmp(word1,"bucket")==0) {
	    printf(" option: hillclimb\n");
	    flag_hillclimb = 1; }
	else if (sscanf(inputline, " weight %d %d", &reset_weight_tries, &weight_update_amt)==2) {
	    printf(" option: use clause weights, reset_weight_tries = %d, weight_update_amt = %d\n", 
		   reset_weight_tries, weight_update_amt); 
	    if (reset_weight_tries == 0){
		crash_maybe(" Error: option 0 for reset_weight_tries not implemented\n");
	    }
	    flag_weigh_clauses = 1; }
	else if (sscanf(inputline, " weight %d", &reset_weight_tries)==1) {
	    printf(" option: use clause weights, reset_weight_tries = %d\n", 
		   reset_weight_tries);
	    if (reset_weight_tries == 0){
		crash_maybe(" Error: option 0 for reset_weight_tries not implemented\n");
	    }
	    flag_weigh_clauses = 1; }
	else if (strcmp(word1,"weight")==0) {
	    printf(" option: use clause weights\n");
	    flag_weigh_clauses = 1; }
	else if (strcmp(word1,"bigflip")==0) {
	    printf(" option: bigflip\n");
	    flag_bigflip = 1; 
	    flag_trace |= FLAG_TRACE_FLIPS;
	    flag_hillclimb = 1; }
	else if (strcmp(word1,"long")==0) {
	    printf(" option: print long report\n");
	    flag_long_report = 1; }
	else if (strcmp(word1,"partial")==0) {
	    printf(" option: partial init file\n");
	    flag_partial = 1; }
	else if (sscanf(inputline, " init %s", init_file)==1)
	    printf(" option: init file %s\n", init_file);
	else if (strcmp(word1,"anneal")==0) {
	    flag_anneal = anneal_parse_parameters(inputline); }
	else if (sscanf(inputline, " adaptive %d", &flag_adaptive)==1) {
	    printf(" option: adaptive initialize with %d modifications\n", flag_adaptive); }
	else if (sscanf(inputline, " plateau %i", &flag_plateau)==1) {
	    printf(" option: plateau = %i\n", flag_plateau); }
	else if (sscanf(inputline, " pause %f", &f)==1) {
	    pause_usecs = (unsigned)(f * 1000000.0);
	    printf(" option: pause = %f\n", f); }
	else if (strcmp(word1,"silent")==0) {
	    printf(" option: silent, reset flag_trace = 0 \n");
	    flag_trace = 0; }
	else if (sscanf(inputline, " trace %d", &option)==1) {
	    flag_trace |= option; 
	    printf(" option: trace += %d, == %d\n", option, flag_trace);
	}
	else if (strcmp(word1, "trace")==0) {
	    if (sscanf(inputline, " %s %s", word1, word2)!=2) {
		crash_maybe(" ERROR: bad trace option\n");
	    }
	    else {
		option = 1;
		for (i=0; i<FLAG_TRACE_NAMES_SIZE; i++){
		    if (strcmp(word2, flag_trace_names[i])==0) break;
		    option = (option << 1);
		}
		if (i==FLAG_TRACE_NAMES_SIZE){
		    crash_maybe(" ERROR: bad trace option\n");
		}
		else {
		    flag_trace += option;
		    printf(" option: trace += %d, == %d\n", option, flag_trace);
		}
	    }
	}

	else if (sscanf(inputline, " r %d", &reset_tries)==1) {
	    printf(" option: reset_tries = %d\n", reset_tries); }
	else if (sscanf(inputline, " report %d", &report_interval)==1) {
	    printf(" option: report_interval = %d\n", report_interval); }
	else if (sscanf(inputline, " seed %d %d", &seed1, &seed2)==2) {
	    printf(" option: seed1 = %d, seed2 = %d\n", seed1, seed2); }
	else if (sscanf(inputline, " seed %d", &seed1)==1) {
	    printf(" option: seed1 = %d\n", seed1); }
	else if (sscanf(inputline, " mask %i", &one_bit_mask)==1) {
	    printf(" option: mask = 0%o\n", one_bit_mask); }
	else if (sscanf(inputline, " best %d", &flag_save_best_max)==1) {
	    printf(" option: save_best_max = %d\n", flag_save_best_max); }
	else if (sscanf(inputline, " tabu %d", &tabu_list_length)==1) {
	    printf(" option: tabu = %d\n", tabu_list_length); }
	else if (sscanf(inputline, " color %i", &flag_coloring)==1) {
	    printf(" option: coloring = %i\n", flag_coloring); }
	else if (sscanf(inputline, " rand %d", &rand_method)==1) {
	    if (rand_method >= 1 && rand_method <= 2){
		printf(" option: rand_method = %d\n", rand_method); }
	    else {
		sprintf(ss, " Error: No rand method %d\n", rand_method);
		crash_maybe(ss);
		rand_method = 1;
	    }}
	else if (sscanf(inputline, " b %d %d", &boost_threshhold, &boost_amount)==2) {
	    printf(" option: boost threshhold = %d, amount = %d\n", boost_threshhold, boost_amount); }
	else if (sscanf(inputline, " c %s", convert_file)==1) {
	    flag_convert = 1;
	    printf(" option: convert and save as %s\n", convert_file); }
	else if (sscanf(inputline, " positive %f", &f)==1) {
	    odds_true = (f * INT_PROB_BASE );
	    printf(" option: probability positive = %f\n", f); }
	else if (sscanf(inputline, " xqueens %s", xtent_pipe)==1) {
	    flag_graphics = FLAG_GRAPHICS_QUEENS;
	    printf(" option: queens graphics using pipe %s\n", xtent_pipe); }
	else if (strcmp(word1,"xgsat")==0) {
	    flag_graphics = FLAG_GRAPHICS_XGSAT;
	    printf(" option: Xgsat graphics\n"); }
	else {
	    sprintf(ss, " ERROR: unknown option %s\n", inputline);
	    crash_maybe(ss);
	}
    }
}

/********************/
/*  Timing          */
/********************/

#ifdef SYSVR4
static struct tms Old_Time;
static struct tms New_Time;
static timerf = 0;
#else
struct rusage gsat_rusage;
long prev_rusage_seconds = 0;
long prev_rusage_micro_seconds = 0;
#endif

double 
elapsed_seconds()
{
  double answer;

#ifdef SYSVR4
  if(!timerf)
    {
      Old_Time.tms_utime = 0;
      timerf = 1;
    }

  times(&New_Time);
  answer = ((double) (New_Time.tms_utime - Old_Time.tms_utime) / CLK_TCK);
  Old_Time.tms_utime = New_Time.tms_utime;

#else
 getrusage(0, &gsat_rusage);//得到进程相关资源信息，存放到gsat_rusage中
  answer = (double)(gsat_rusage.ru_utime.tv_sec - prev_rusage_seconds)
    + ((double)(gsat_rusage.ru_utime.tv_usec - prev_rusage_micro_seconds)) / 
      1000000.0 ;//gsat_rusage.ru_utime是user CPU time used,所以说函数叫“过去的时间”，因为answer里计算的是这次的ru_utime-上次的ru_utime
  prev_rusage_seconds = gsat_rusage.ru_utime.tv_sec ;
  prev_rusage_micro_seconds = gsat_rusage.ru_utime.tv_usec ;
#endif

  return answer;
}

/********************/
/*  Graphics        */
/********************/

void
queens_open_pipe()
{
    if ((fp_xtent = fopen(xtent_pipe, "w"))==NULL){
	sprintf(ss, "ERROR: cannot open xtent pipe %s\n", xtent_pipe);
	crash_and_burn(ss);
    }
}


void
queens_show_variable_state(PROTO(int) var, PROTO(int) val)
PARAMS(int var; int val;)
{
    if (val != -1)
      fprintf (fp_xtent, "xtent.XtAdd: %d\n", var);
    else
      fprintf (fp_xtent, "xtent.XtRemove: %d\n", var);
    fflush (fp_xtent); 
}

void
queens_clear()
{
    fprintf (fp_xtent, "xtent.XtClear:\n");
    fflush (fp_xtent);
}


/* General graphics routines; main code should call only these */

void
graphics_init(PROTO(char **) argv, PROTO(int) argc)
PARAMS( char ** argv; int argc; )
{
    if (flag_graphics == FLAG_GRAPHICS_QUEENS) queens_open_pipe();
#ifdef XGSAT
    else if (flag_graphics == FLAG_GRAPHICS_XGSAT) 
      xgsat_init(argv, argc, nvars, nclauses, NULL);
#endif
}

void
graphics_show_variable(PROTO(int) var, PROTO(int) flipping)
PARAMS(int var; int flipping;)
     /* If flipping is TRUE, then called when flipping, else 
	called when initializing */
{
    int val;

    val = assign[var].value;
    if (flag_graphics == FLAG_GRAPHICS_QUEENS) queens_show_variable_state(var, val);
#ifdef XGSAT
    else if (flag_graphics == FLAG_GRAPHICS_XGSAT){
	if (flipping) xgsat_show_flip_and_unsat( flip, current_num_bad);
	xgsat_show_var_state(var, val, flipping);
    }
#endif
}

void
graphics_end_try_initialization()
{
#ifdef XGSAT
    if (flag_graphics == FLAG_GRAPHICS_XGSAT){    
	xgsat_show_flip_and_unsat( 0, current_num_bad );
    }
#endif
}

void
graphics_start_flip()
{
#ifdef XGSAT
    if (flag_graphics == FLAG_GRAPHICS_XGSAT){    
	xgsat_pause_maybe();
	if (xgsat_command == XGSAT_STEP) xgsat_command = XGSAT_STOP;
	xgsat_wait_for_var(&xgsat_command);
	if (xgsat_command == XGSAT_QUIT){
	    main_wrapup("XGSAT Quit pushed during a try");
	    exit(-1); /* Not reached */
	}
    }
#endif
}

void
graphics_start_try()
{
#ifdef XGSAT
    if (flag_graphics == FLAG_GRAPHICS_XGSAT){
	if (xgsat_command == XGSAT_GO ||
	    xgsat_command == XGSAT_STEP ) xgsat_command = XGSAT_STOP;
	xgsat_wait_for_var(&xgsat_command);
	if (xgsat_command == XGSAT_QUIT){
	    main_wrapup("XGSAT Quit pushed before a try");
	    exit(-1); /* Not reached */
	}
	xgsat_show_flip_and_unsat( 0, nclauses );
	xgsat_show_all(0);
    }
#endif
}

void
graphics_show_clause_state(PROTO(int) clause_num, PROTO(int) val)
PARAMS(int clause_num; int val;)
{
#ifdef XGSAT
    if (flag_graphics == FLAG_GRAPHICS_XGSAT){
	xgsat_show_clause_state(clause_num, val, 1);
    }
#endif
}

void
graphics_terminate()
{
#ifdef XGSAT
    if (flag_graphics == FLAG_GRAPHICS_XGSAT)
      xgsat_do_events_forever();
#endif
}


/********************/
/*  Printing        */
/********************/

int
lit_of_clause_num( PROTO(int) lit_num, PROTO(int) clause_num)
PARAMS( int lit_num; int clause_num; )
{
    if (clause_num_to_index == NULL)
      crash_and_burn("ERROR: clause_num_to_index not initialized\n");
    if (clause_num < 1 || clause_num > nclauses)
      crash_and_burn("ERROR: clause_num out of range\n");
    if (lit_num < 1 || lit_num > length_of_clause_num(clause_num))
      crash_and_burn("ERROR: lit_num out of range\n");
    return (wff[ clause_num_to_index[clause_num] + lit_num ].lit );
}

int
length_of_clause_num(PROTO(int) clause_num)
PARAMS( int clause_num; )
{
    if (clause_num_to_index == NULL)
      crash_and_burn("ERROR: clause_num_to_index not initialized\n");
    if (clause_num < 1 || clause_num > nclauses)
      crash_and_burn("ERROR: clause_num out of range\n");
    return (wff[ clause_num_to_index[clause_num] ].lit );
}


void
trace_clause_state(PROTO(int) clause_index, PROTO(int) state)
PARAMS(int clause_index; int state;)
{
    int clause_num;

    if ((clause_num = clause_index_to_num[clause_index]) <= 0){
	sprintf(ss, "ERROR: Bad entry clause_index_to_num[%d] == %d\n", 
		clause_index, clause_index_to_num[clause_index]);
	crash_and_burn(ss);
    }
    
    if (flag_trace & FLAG_TRACE_CLAUSE_STATE){
	if (state == 1)
	  printf("Becomes GOOD: %d\n", clause_num);
	else if (state == -1)
	  printf("Becomes BAD: %d\n", clause_num);
	else
	  printf("Becomes UNKNOWN: %d\n", clause_num);
    }
    if (flag_graphics)
	graphics_show_clause_state(clause_num, state);
}

void
print_wff()  /* print the raw wff array */
{
  int i;
  printf("raw wff:\nindex  lit   next\n");
  for (i=1; i<=(nlits + nclauses) && i<=MAX_DIAGNOSTICS; i++){
    printf("  %d      %d       %d\n", i, wff[i].lit, wff[i].next);
  }
}


void
print_offset_clause(PROTO(int) clause_index, PROTO(int) offset)
PARAMS(int clause_index;)
PARAMS(int offset;)
{
  int clause_len, i;
  int lit;

  clause_len = wff[clause_index].lit;
  for (i=1; i<=clause_len; i++){
      lit = wff[clause_index + i].lit;
      if (lit < 0) {
	  printf(" %d ", lit - offset);
      }
      else {
	  printf(" %d ", lit );
      }
  }
  printf("\n");
}

void
print_clause(PROTO(int) clause_index)
PARAMS(int clause_index;)
{
    print_offset_clause(clause_index, 0);
}

void
print_wff_clauses()  /* print the wff in clausal form */
{
  int clause_index, i;

  printf("wff clauses:\n");
  
  clause_index=1;
  for (i = 1; i <= nclauses && i<=MAX_DIAGNOSTICS; i++){
    printf("clause %d is ", i);
    print_clause(clause_index);
    clause_index += 1 + wff[clause_index].lit;
  }
}


void
print_try_statistics()  /* print stats on most recent try */
{
    if (flag_trace){
	printf("TRY %d: init_bad=%d, max_flips=%d, max_diff=%d, num_bad=%d, low_bad=%d, d=%d s=%d u=%d n=%d\n",
	       current_try, init_bad, max_flips,
	       current_max_diff, current_num_bad, low_bad, downwards_count,
	       sideways_count, upwards_count, null_count);
    }
    fprintf(try_stat_filep, "TRY %d: init_bad=%d, max_flips=%d, max_diff=%d, num_bad=%d, low_bad=%d, d=%d s=%d u=%d n=%d\n",
	    current_try, init_bad, max_flips,
	    current_max_diff, current_num_bad, low_bad, downwards_count,
	    sideways_count, upwards_count, null_count);
}

void
print_best_statistics()  /* print stats on best try */
{
    printf("\n\nDATA on BEST assignment stored\n");
    printf("best_flip:             %d\n", best_flip);
    printf("best_try:              %d\n", best_try);
    printf("best_num_bad:          %d\n", best_num_bad);
    printf("best_max_diff:         %d\n", best_max_diff);
    printf("best_downwards:        %d\n", best_downwards);
    printf("best_sideways:         %d\n", best_sideways);
    printf("best_upwards:          %d\n", best_upwards);
    printf("best_null:             %d\n", best_null);
}

void
print_bad_clause_count(PROTO(FILE *) fp_report)
PARAMS(FILE *fp_report;)
{
    int i, num;
    fprintf(fp_report, "Distribution of bad_clause_count:\n");
    fprintf(fp_report, "     bad:         tries:\n");

    for (i = 0; i <= 10; i++)
      fprintf(fp_report, "    %3d           %4d\n",       
	      i, bad_clause_count[i].value);

    for (i = 11; i <= LENGTH_BAD_CLAUSE_COUNT; i++)
      if (bad_clause_count[i].value != 0) {
	  if (i <= 19) fprintf(fp_report, "    %3d           %4d\n", 
			       i, bad_clause_count[i].value);
	  else if ( i < LENGTH_BAD_CLAUSE_COUNT ) {
	      num = ((i - 20) * 10 ) + 20;
	      fprintf(fp_report, "    %3d -- %3d    %4d\n", 
		      num, (num + 9) , bad_clause_count[i].value);}
	  else 
	    fprintf(fp_report, "    %3d -- ***    %4d\n", 
		    (20 + (LENGTH_BAD_CLAUSE_COUNT - 20) * 10),
		    bad_clause_count[i].value);
      }
    fprintf(fp_report, "End of distribution\n\n");
}

void
print_reset_bad_clause_count(PROTO(FILE *) fp_report)
PARAMS(FILE *fp_report;)
{
    int i, num;
    fprintf(fp_report, "Distribution of reset_bad_clause_count:\n");
    fprintf(fp_report, "     bad:         reset_groups:\n");

    for (i = 0; i <= 10; i++)
      fprintf(fp_report, "    %3d           %4d\n",       
	      i, reset_bad_clause_count[i].value);

    for (i = 11; i <= LENGTH_BAD_CLAUSE_COUNT; i++)
      if (reset_bad_clause_count[i].value != 0) {
	  if (i <= 19) fprintf(fp_report, "    %3d           %4d\n", 
			       i, reset_bad_clause_count[i].value);
	  else if ( i < LENGTH_BAD_CLAUSE_COUNT ) {
	      num = ((i - 20) * 10 ) + 20;
	      fprintf(fp_report, "    %3d -- %3d    %4d\n", 
		      num, (num + 9) , reset_bad_clause_count[i].value);}
	  else 
	    fprintf(fp_report, "    %3d -- ***    %4d\n", 
		    (20 + (LENGTH_BAD_CLAUSE_COUNT - 20) * 10),
		    reset_bad_clause_count[i].value);
      }
    fprintf(fp_report, "End of distribution\n\n");
}


void
print_variable_statistics(PROTO(FILE *) fp_report)
PARAMS(FILE *fp_report;)
{
    int i, c, n;
    double a;

    fprintf(fp_report,"Variable statistics:\n");
    fprintf(fp_report,"     var     positive   %% pos  flip_count\n");
    n = total_sum_tries;
    
    for (i = 1; i <= nvars; i++) {
	c = assign[i].positive_count;
	a = ((double)c)/n;
	fprintf(fp_report, "  %6d    %6d    %6d    %6d\n", 
		i, c, ((int)(100*a)), assign[i].flip_count);
    }
    fprintf (fp_report,"End of variable statistics\n\n");
}

void
print_weights(PROTO(FILE *) fp_report)
PARAMS(FILE *fp_report;)
{
    int i, j, clause_len, clause_index;

    fprintf(fp_report,"Clauses_weights (> 1):\n");
    fprintf(fp_report,"  clause   X weight   contents\n");

    clause_index = 1;
    for (i = 1; i <= nclauses; i++) {
	if (wff[clause_index].next > 1){
	    fprintf(fp_report, " %6d    x %6d    ", i, wff[clause_index].next);
	    clause_len = wff[clause_index].lit;
	    for (j=1; j<=clause_len; j++){
		fprintf(fp_report, " %d ", wff[clause_index + j].lit);
	    }
	    fprintf(fp_report, "\n");
	}
	clause_index += wff[clause_index].lit + 1;
    }
    fprintf(fp_report,"End of clause_weights\n\n");
}

void
print_positive_literals(PROTO(FILE *) fp)
PARAMS(FILE *fp;)
{
    int i,k;

    fprintf(fp,"Positive literals in best model:\n");
    k=1;
    for (i = 1; i <= nvars; i++) {
	if (assign[i].value_best == 1){
	    fprintf(fp," %d ", (i * assign[i].value_best));
	    k++;
	    if ((k%LINE_LENGTH) == 0) fprintf(fp,"\n ");
	}
    }
    fprintf (fp,"\nEnd of best model\n\n");
}

void
print_unsat_clauses(PROTO(FILE *) fp)
     /* Print the unsatisfied clauses in the best assignment found.
	This code modifies that used in get_bad_clauses, and handles
	the flag_coloring option. */
PARAMS(FILE *fp;)
{
    int i, clause_len, j, clause_index;
    wff_str_ptr clause_ptr;
    int bad, lit, offset;

    fprintf(fp,"Unsat clauses in best model:\n");
    for (offset=0; (offset==0) || (offset < flag_coloring); offset++){
	clause_index = 1;
	for (i = 1; i <= nclauses; i++) {
	    clause_ptr = &wff[clause_index];
	    clause_len = clause_ptr->lit;
	    clause_ptr++;

	    if ((offset == 0) || (clause_ptr->lit < 0)) { /* Only use offsets on negative clauses */
		bad = 1;
		for (j = 1; j <= clause_len; j++){
		    if (assign[abs_val(clause_ptr->lit) + offset ].value_best * clause_ptr->lit > 0 ) {
			bad = 0;
			break;
		    }
		    clause_ptr++;
		}
		if (bad) {
		    for (j=1; j<=clause_len; j++){
			lit = wff[clause_index + j].lit;
			if (lit<0)
			  lit -= offset;
			else
			  lit += offset;
			fprintf(fp, " %d ", lit);
		    }
		    fprintf(fp, "\n");
		}
		clause_index += clause_len + 1;
	    }
	}
    }
    fprintf (fp,"End of unsat clauses\n\n");
}

void
print_report( PROTO( char *) message )
PARAMS( char * message;)
{
    FILE *fp_report;
    int c;

    if ((fp_report = fopen(report_file, "w"))== NULL){
	sprintf(ss, "ERROR: cannot open report file %s\n", report_file);
	crash_and_burn(ss);
    }

    if (message != NULL){
	fprintf(fp_report, "TRY %d: ", current_try);
	fprintf(fp_report, message);
	fprintf(fp_report, "\n\n");
    }

    fprintf(fp_report, "REPORT START\n");
    fprintf(fp_report, program_name);
    fprintf(fp_report, "host: %s\n", hostname);
    fprintf(fp_report, "machine: %s\n", hostutsname.machine);
    fprintf(fp_report, "date: %s\n", datestring);

    fprintf(fp_report, "wff_file: %s\n", wff_file);
    fprintf(fp_report, "nvars (number of variables): %d\n", nvars);
    fprintf(fp_report, "nclauses (number of clauses): %d\n", nclauses);
    fprintf(fp_report, "nlits (length of wff): %d\n", nlits);

    fprintf(fp_report, "assign_file: %s\n", assign_file);  
    fprintf(fp_report, "report_file: %s\n", report_file);
    fprintf(fp_report, "max_flips: %d\n", max_flips);
    fprintf(fp_report, "max_tries: %d\n\n", max_tries);
    fprintf(fp_report, "seed1: %d\n", seed1);
    fprintf(fp_report, "seed2: %d\n", seed2);

    if (init_file[0]) fprintf(fp_report, "init_file: %s\n", init_file);
    if (flag_partial) fprintf(fp_report, "flag_partial: %d\n", flag_partial);
    if (reset_tries != 1){
	fprintf(fp_report, "reset_tries: %d\n", reset_tries);
	fprintf(fp_report, "flips_per_reset: %d\n", reset_tries * max_flips);
    }
    if (flag_superlinear) fprintf(fp_report, "flag_superlinear: %d\n", flag_superlinear);
    if (flag_init_prop) fprintf(fp_report, "flag_init_prop: %d\n", flag_init_prop);
    if (flag_walk) fprintf(fp_report, "walk: %f\n", ((double)flag_walk)/INT_PROB_BASE);
    if (flag_walk_all_vars) fprintf(fp_report, "flag_walk_all_vars: %d\n", flag_walk_all_vars);
    if (flag_only_unsat) fprintf(fp_report, "flag_only_unsat: %d\n", flag_only_unsat);
    if (flag_direction) fprintf(fp_report, "flag_direction: %d\n", flag_direction);
    if (flag_plateau) fprintf(fp_report, "flag_plateau: %d\n", flag_plateau);
    if (flag_hole) fprintf(fp_report, "flag_hole: %d\n", flag_hole);
    if (flag_hole_continue) fprintf(fp_report, "flag_hole_continue: %d\n", flag_hole_continue);
    if (flag_multiple_assigns) fprintf(fp_report, "flag_multiple_assign: %d\n", flag_multiple_assigns);
    if (boost_threshhold){
	fprintf(fp_report, "boost_threshhold: %d\n", boost_threshhold);
	fprintf(fp_report, "boost_amount: %d\n", boost_threshhold);
    }
    if (rand_method != 1) fprintf(fp_report, "rand_method: %d\n", rand_method);
    if (one_bit_mask != DEFAULT_ONE_BIT_MASK) fprintf(fp_report, "mask: 0%o\n", one_bit_mask);
    if (odds_true != INT_PROB_BASE / 2) fprintf(fp_report, "positive: %f\n", ((double)odds_true)/INT_PROB_BASE);
    if (flag_coloring) fprintf(fp_report, "flag_coloring: %d\n", flag_coloring);
    if (flag_weigh_clauses){
	fprintf(fp_report, "flag_weigh_clauses: %d\n", flag_weigh_clauses);
	fprintf(fp_report, "reset_weight_tries: %d\n", reset_weight_tries);
	fprintf(fp_report, "weight_update_amt: %d\n", weight_update_amt);
    }
    if (flag_anneal) fprintf(fp_report, "flag_anneal: %d\n", flag_anneal);
    if (flag_bigflip) fprintf(fp_report, "flag_bigflip: %d\n", flag_bigflip);
    if (flag_save_best_max!=SAVE_BEST_MAX_DEFAULT) fprintf(fp_report, "flag_save_best_max: %d\n", flag_save_best_max);
    if (flag_adaptive) fprintf(fp_report, "flag_adaptive: %d\n", flag_adaptive);
    if (tabu_list_length) fprintf(fp_report, "tabu_list_length: %d\n", tabu_list_length);
    if (flag_hillclimb) fprintf(fp_report, "flag_hillclimb: %d\n\n", flag_hillclimb);

    fprintf(fp_report, "total_num_assigns (number of assignments found): %d\n", total_num_assigns);
    fprintf(fp_report, "total_sum_flips: %d\n", total_sum_flips);
    fprintf(fp_report, "total_sum_tries: %d\n", total_sum_tries);
    fprintf(fp_report, "total_sum_successful_flips: %d\n", total_sum_successful_flips);
    fprintf(fp_report, "total_downwards: %d\n", total_downwards);
    fprintf(fp_report, "total_upwards: %d\n", total_upwards);
    fprintf(fp_report, "total_sideways: %d\n", total_sideways);
    fprintf(fp_report, "total_null: %d\n\n", total_null);

    fprintf(fp_report, "percent_downwards: %6.3f\n", ((float) total_downwards) / total_sum_flips);
    fprintf(fp_report, "percent_upwards:   %6.3f\n", ((float) total_upwards) / total_sum_flips);
    fprintf(fp_report, "percent_sideways:  %6.3f\n", ((float) total_sideways) / total_sum_flips);
    fprintf(fp_report, "percent_null:      %6.3f\n\n", ((float) total_null) / (total_sum_flips + total_null));

    fprintf(fp_report, "experiment_seconds: %f\n\n", experiment_seconds);

    fprintf(fp_report, "assigns_per_second: %f\n", total_num_assigns / experiment_seconds);
    fprintf(fp_report, "flips_per_second: %f\n", total_sum_flips / experiment_seconds);
    fprintf(fp_report, "tries_per_second: %f\n", total_sum_tries / experiment_seconds);
    fprintf(fp_report, "assignments_per_try: %f\n", 
	    (float)total_num_assigns / total_sum_tries);
    fprintf(fp_report, "successful_flips_per_flip (ratio productive effort): %f\n", 
	    (float)total_sum_successful_flips / total_sum_flips);
    fprintf(fp_report, "average_after_init_num_bad: %f\n", ((float) total_after_init_num_bad) / total_sum_tries);
    fprintf(fp_report, "total_successful_flips_incl_resets: %d\n", total_successful_flips_incl_resets);
    fprintf(fp_report, "total_successful_reset_count: %d\n\n", total_successful_reset_count);

    if (total_num_assigns > 0) {
	fprintf(fp_report, "ASSIGNMENT FOUND\n\n");
	fprintf(fp_report, "seconds_per_assign: %f\n", 
		experiment_seconds / total_num_assigns);
	fprintf(fp_report, "successful_flips_per_assign: %f\n", 
		(float) total_sum_successful_flips / total_num_assigns);
	fprintf(fp_report, "successful_flips_incl_resets_per_assign: %f\n", 
		(float) total_successful_flips_incl_resets / total_num_assigns);
	fprintf(fp_report, "flips_per_assign: %f\n", 
		(float) total_sum_flips / total_num_assigns);
	fprintf(fp_report, "average_reset_count_each_assign: %f\n", 
		(float) total_successful_reset_count / total_num_assigns);
	fprintf(fp_report, "tries_per_assign: %f\n", 
		(float) total_sum_tries / total_num_assigns);
	fprintf(fp_report, "flips_per_successful_flip: %f\n\n", 
		(float) total_sum_flips / total_sum_successful_flips);
    }
    else {
	fprintf(fp_report, "NO ASSIGNMENT FOUND\n\n");
    }

    print_bad_clause_count(fp_report);
    print_reset_bad_clause_count(fp_report);

    fprintf(fp_report, "best_flip:              %d\n", best_flip);
    fprintf(fp_report, "best_try:               %d\n", best_try);
    fprintf(fp_report, "best_num_bad:           %d\n", best_num_bad);
    fprintf(fp_report, "best_max_diff:          %d\n", best_max_diff);
    fprintf(fp_report, "best_downwards:         %d\n", best_downwards);
    fprintf(fp_report, "best_sideways:          %d\n", best_sideways);
    fprintf(fp_report, "best_upwards:           %d\n", best_upwards);
    fprintf(fp_report, "best_null:              %d\n", best_null);
    fprintf(fp_report, "best_reset_count:       %d\n", best_reset_count);
    fprintf(fp_report, "best_flips_incl_resets: %d\n\n", 
	    ((best_reset_count-1)*max_flips)+best_flip);

    if (flag_anneal) anneal_print_report(fp_report);

    print_positive_literals(fp_report);

    if (flag_long_report){
	print_unsat_clauses(fp_report);
	print_weights(fp_report);
	print_variable_statistics(fp_report);
    }

    fprintf(fp_report, "\nTRY STATISTICS:\n");

    fflush(try_stat_filep);
    rewind(try_stat_filep);
    while ((c=fgetc(try_stat_filep))!=EOF)
      fputc(c, fp_report);
    fflush(try_stat_filep);
    fseek(try_stat_filep, 0, SEEK_END);

    fprintf(fp_report, "\nREPORT END\n");
    fclose(fp_report);
}

void
print_assignment_file()
{
    int i, k ;
    FILE *fp;

    if ((fp = fopen(assign_file, "w"))==NULL) {
	sprintf(ss, "ERROR: cannot open assign file %s\n", assign_file);
	crash_and_burn(ss);
    }
    fprintf(fp, ";;; ");
    fprintf(fp, program_name);
    fprintf(fp, "(setq *gsat-wff-file* \"%s\")\n", wff_file);
    fprintf(fp, "(setq *gsat-nvars* %d)\n", nvars);
    fprintf(fp, "(setq *gsat-nclauses* %d)\n", nclauses);
    fprintf(fp, "(setq *gsat-nlits* %d)\n", nlits);
    fprintf(fp, "(setq *gsat-max-flips* %d)\n", max_flips);
    fprintf(fp, "(setq *gsat-max-tries* %d)\n\n", max_tries);

    fprintf(fp, "(setq *gsat-best-num-bad* %d)\n", best_num_bad);
    if (best_num_bad == 0 ) 
      fprintf(fp,"(setq *gsat-assign-found* t )\n\n");
    else
      fprintf(fp,"(setq *gsat-assign-found*  nil )\n\n");
    
    fprintf(fp,";;; List of positive literals in the model\n");
    fprintf (fp,"(setq *gsat-model-list* '( \n ");
    k=1;
    for (i = 1; i <= nvars; i++) {
	if (assign[i].value_best == 1){
	    fprintf(fp," %d ", (i * assign[i].value_best));
	    k++;
	    if ((k%LINE_LENGTH) == 0) fprintf(fp,"\n ");
	}
    }
    fprintf (fp,"\n ))\n\n");
    
    fprintf(fp,";;; Model vector; first element not used\n");
    fprintf (fp,"(setq *current-propositional-model* (vector 0 \n ");
    for (i = 1; i <= nvars; i++) {
	if (assign[i].value_best > 0) fprintf(fp," 1 ");
	else fprintf(fp, " 0 ");
	if ((i%LINE_LENGTH) == 0) fprintf(fp,"\n ");
    }
    fprintf (fp,"\n ))\n\n");
    

    fclose(fp);
}

void
print_assign_stdout()
{
    int i, k;
    printf("Positive literals:");
    k = 0;
    for (i = 1; i <= nvars; i++) {
	if (assign[i].value == 1){
	    printf(" %d ", i);
	    k++;
	    /* if ((k%LINE_LENGTH) == 0) printf("\n"); */
	}
    }
    printf("\n");
}



/********************/
/* Signaled Quit    */
/********************/

/* ANSI signal definition:

   void (*signal(int signum, void (*sighandler)(int)))(int)

   What system uses the other version?
*/


/* #ifdef SYSVR4
   void
   handle_interrupt(PROTO(int) sig)
   PARAMS(int sig;)
   #else
*/
void
handle_interrupt(PROTO(int) sig)
PARAMS(int sig;)
/* #else
  void
  handle_interrupt(PROTO(int) sig, PROTO(int) code, PROTO(struct sigcontext *) scp, 
		 PROTO(char *) addr)
  PARAMS(int sig; int code; struct sigcontext * scp; char * addr;)
  #endif
*/
{
  /* If kill or quit received, print */
  /* out report before exiting */

    char inputline[MAXLINE];
    int c;

    /* Don't block interrupts! */
#ifdef SYSVR4
    sigsetmask(0);
#endif

    if (flag_abort == 0) {
	printf("\n\nShhh!\n");
	flag_abort = -1;
	flag_trace = 0;
    }
    else if (flag_abort == -1){
	experiment_seconds += elapsed_seconds();
	flag_abort = 1;
	print_report("KEYBOARD INTERRUPT");
	elapsed_seconds();
	printf("\nReport printed -- keep going? [y or n] ");
	if (fgets(inputline, MAXLINE, stdin)==NULL){
	    inputline[0]='n';
	}
	while (((c=inputline[0])!='y') && c != 'n' && c != EOF && c != '\003' ){
	    printf("\nType 'y' or 'n' followed by return: ");
	    if (fgets(inputline, MAXLINE, stdin)==NULL){
		inputline[0]='n';
	    }
	}
	if (c == 'y'){
	    flag_abort = -1;
	    printf("\nOkay, I'll continue working.\n");   
	}
    }

    if (flag_abort == 1){
	printf("\nOuch! Ouch! Ouch!\n");
	exit(-1);
    }	


    signal(SIGINT, handle_interrupt);
    if(signal(SIGQUIT, SIG_IGN) != SIG_IGN)
      signal(SIGQUIT, handle_interrupt);
    signal(SIGTERM, handle_interrupt);
}
     
/**************************/
/*  Converting Wff Format */
/**************************/

void
output_f_format(PROTO(FILE *) fp)
PARAMS(FILE *fp;)
{
    int i, j, index, clause_len;

    index = 1;
    for (i=1; i<=nclauses; i++) {
	clause_len = wff[index].lit;
	for (j=1; j<= clause_len; j++){
	    fprintf(fp, " %d", wff[index+j].lit);
	}
	index += clause_len + 1;
	fprintf(fp, "\n");	
    }
    fprintf(fp, "%%\n0\n");
}

void
output_f_lisp_format(PROTO(FILE *) fp)
PARAMS(FILE *fp;)
{
    int i, j, index, clause_len;

    index = 1;
    for (i=1; i<=nclauses; i++) {
	clause_len = wff[index].lit;
	fprintf(fp, "(");
	for (j=1; j<= clause_len; j++){
	    fprintf(fp, " %d", wff[index+j].lit);
	}
	index += clause_len + 1;
	fprintf(fp, ")\n");	
    }
}

void
output_kf_format(PROTO(FILE *) fp)
PARAMS( FILE *fp; )
{
    int i, j, index, clause_len;

    fprintf(fp, "%d %d\n", nvars, nclauses);
    index = 1;
    for (i=1; i<=nclauses; i++) {
	clause_len = wff[index].lit;
	fprintf(fp, "%d ", clause_len);
	for (j=1; j<= clause_len; j++){
	    fprintf(fp, " %d ", wff[index+j].lit);
	}
	fprintf(fp, "\n");
	index += clause_len + 1;
    }
}

void
output_cnf_format(PROTO(FILE *) fp)
PARAMS( FILE *fp; )
{
    int i, j, index, clause_len;

    fprintf(fp, "p cnf %d %d\n", nvars, nclauses);
    index = 1;
    for (i=1; i<=nclauses; i++) {
	clause_len = wff[index].lit;
	for (j=1; j<= clause_len; j++){
	    fprintf(fp, "%d ", wff[index+j].lit);
	}
	fprintf(fp, "0\n");
	index += clause_len + 1;
    }
}

void
output_converted_wff()
{
    FILE *fp;
    if ((fp = fopen(convert_file, "w"))==NULL) {
	sprintf(ss, "ERROR: cannot open output file %s\n", convert_file);
	crash_and_burn(ss);
    }

    if (0==strcmp(".f", &(convert_file[strlen(convert_file)-2])))
      output_f_format(fp);
    else if (0==strcmp(".np", &(convert_file[strlen(convert_file)-3])))
      output_f_format(fp);
    else if (0==strcmp(".kf", &(convert_file[strlen(convert_file)-3])))
      output_kf_format(fp);
    else if (0==strcmp(".cnf", &(convert_file[strlen(convert_file)-4])))
      output_cnf_format(fp);
    else if (0==strcmp(".lisp", &(convert_file[strlen(convert_file)-5])))
      output_f_lisp_format(fp);
    else if (flag_format == FLAG_FORMAT_KF)
      output_f_format(fp);
    else if (flag_format == FLAG_FORMAT_F || flag_format == FLAG_FORMAT_LISP)
      output_kf_format(fp);
    else if (flag_format == FLAG_FORMAT_CNF)
      output_f_format(fp);

    fclose(fp);
}

/**************************/
/*  Keeping Statistics    */
/**************************/

void
save_current_as_best()
     /* Current assignment is best found so far */
{
    int i;
    var_str_ptr vp;

    if (flag_trace & FLAG_TRACE_BEST){
	printf("BEST for all tries is %d on flip %d of try %d\n", 
	       current_num_bad, flip, current_try);
    }

    best_num_bad = current_num_bad;
    best_max_diff = current_max_diff;
    best_flip = flip;
    best_try = current_try;
    best_downwards = downwards_count;
    best_sideways = sideways_count;
    best_upwards = upwards_count;
    best_null = null_count;
    best_reset_count = ((try_this_assign - 1) % reset_tries) + 1;
    for (i = 1, vp= &assign[1]; i <= nvars; i++, vp++) {
	vp->value_best = vp->value;
    }
}

void
save_current_as_low()
     /* Current assignment is best found in current try */
{
    int i;
    var_str_ptr vp;

    if (flag_trace & FLAG_TRACE_BEST){
	printf("LOW for try is %d on flip %d\n", current_num_bad, flip);
    }

    for (i = 1, vp= &assign[1]; i <= nvars; i++, vp++) {
	vp->value_low = vp->value;
    }
}

void
update_bad_clause_count( PROTO(int) num)
PARAMS( int num; )
{   
    int tmp;

    if (num <= 19)
      bad_clause_count[num].value++;
    else if ((num > 19) && 
             (num < (((LENGTH_BAD_CLAUSE_COUNT - 20) * 10) + 20))){
	tmp = ifloor(((double)(num - 20)) / 10.0) + 20;
	if (tmp >= LENGTH_BAD_CLAUSE_COUNT){ 
	    crash_and_burn("Error in update_bad_clause_count\n");
	}
	bad_clause_count[tmp].value++;}
    else
      bad_clause_count[LENGTH_BAD_CLAUSE_COUNT].value++;
}

void
update_reset_bad_clause_count( PROTO(int) num)
PARAMS( int num; )
{   
    int tmp;

    if (num <= 19)
      reset_bad_clause_count[num].value++;
    else if ((num > 19) && 
             (num < (((LENGTH_BAD_CLAUSE_COUNT - 20) * 10) + 20))){
	tmp = ifloor(((double)(num - 20)) / 10.0) + 20;
	if (tmp >= LENGTH_BAD_CLAUSE_COUNT){ 
	    crash_and_burn("Error in update_reset_bad_clause_count\n");
	}
	reset_bad_clause_count[tmp].value++;}
    else
      reset_bad_clause_count[LENGTH_BAD_CLAUSE_COUNT].value++;
}

void
update_positive_count()
{
    int i;
    var_str_ptr vp;

    for (i = 1, vp= &assign[1]; i <= nvars; i++, vp++) {
	if (vp->value == 1) vp->positive_count++;
    }
}

/********************/
/*  Random          */
/********************/

void
init_rand()  /* create more random bits */
{
  struct timeval tv;
  struct timezone tzp;
  int sec, msec;

  gettimeofday(&tv,&tzp);//tzp在现代的linux中没用了，为NULL
  sec = (int) tv.tv_sec;//sec秒数,usec微秒数，进行计时前后两次调用gettimeofday计算中间的差值
  msec = (int) tv.tv_usec;
  //add by YZ
   sec = 1334055194;
   msec = 197896;
  //sec = 1335356963;
  //msec = 674949;
  printf("sec: %d  usec: %d\n", sec, msec);

  if (rand_method == 1){
      if (seed1 == 0) {
	  /* Use just the lower 7 bits of sec == approx 2 minutes */
	  seed1 = (( sec & 0177 ) * 1000000) + msec;//八进制在数的最高位加0,0117即十进制127,用sec的低7位秒数并换算成微妙10^6，与msec相加得到seed1
      }
      seed2 = 0;
#ifdef SYSVR4
      srand48(seed1);
#else
      srandom(seed1);
#endif
  }
  else {
      if (seed1 == 0 && seed2 == 0) {
	  /* Following gives approximately 27 bits */
	  seed1 = (( sec & 0177 ) * 1000000) + msec;
	  /* Divide bits among the two seeds */
	  seed2 = seed1 & 03777;
	  seed1 = seed1 >> 14;
      }
      rd = uopen();
      useed(rd, seed1, seed2);
  }
  printf("Random seed: %10d  %10d\n", seed1, seed2);
}


int
random_1_to(PROTO(int) n)	/* Return random number 1..n */
PARAMS(int n;)
{
    long r;

    if (rand_method == 1)
#ifdef SYSVR4
      r = lrand48();
#else
      r = random();
#endif

    else
      r = urand(rd);

    return ((r >> 9) % n) + 1;
}

int
random_01_odds(PROTO(int) odds)  /* odds(机率) is relative to INT_PROB_BASE=10000000  */
PARAMS(int odds;)
{
    long r;

    if (rand_method == 1)
#ifdef SYSVR4
      r = lrand48();
#else
      r = random();
#endif
    else
      r = urand(rd);
    
    if ((r % INT_PROB_BASE) < odds)
      return 1;
    else 
      return 0;
}

/********************/
/*  Initializing    */
/********************/

void
allocate_memory()
{
    wff = (wff_str_ptr) malloc ((size_t)((nlits + nclauses + 1) * (sizeof(struct wff_str))));//wff数组的lit依次存放本子句字母（变量）数，然后依次放本子句各字母变量，然后下一条子句同样。所以wff的大小是nvars+nclause+1

    assign = (var_str_ptr) malloc ((size_t)(nvars + 1) * (sizeof(struct var_str)));
    bad_clause_count = (bad_clause_count_str_ptr) 
      malloc ((size_t)((LENGTH_BAD_CLAUSE_COUNT + 1)* 
	      (sizeof(struct bad_clause_count_str))));
    reset_bad_clause_count = (bad_clause_count_str_ptr) 
      malloc ((size_t)((LENGTH_BAD_CLAUSE_COUNT + 1)* 
	      (sizeof(struct bad_clause_count_str))));
}

int
white(PROTO(int) c)
PARAMS( int c; )
{
    return (c==' ' || c=='\n' || c=='\t' || c=='\f');
}

int
space_or_paren(PROTO(int) c)
PARAMS( int c; )
{
    return (c==' ' || c=='(' || c=='\t' || c==')');
}



int
read_in_f_format()	
{
    FILE *fp;
    int c;
    char field[MAXLINE];
    int index, wffindex, clause_start, clause_length;
    int lit, var;
    int i, tautologous_clause, repeated_literal;
    int clause_number;
    
    nvars = 0;
    nclauses = 0;
    nlits = 0;

    printf("Trying to read f-format input\n");

    /* Scan once to calculate nvars, nlits, nclauses */
    if ((fp = fopen(wff_file, "r"))==NULL){
	sprintf(ss, "ERROR: cannot open wff file %s\n", wff_file);
	crash_and_burn(ss);
    }

    c = ' ';
    while (space_or_paren(c)) c=getc(fp);
    while (c != EOF && c != '%'){
	nclauses ++;
	if (c==EOF){ fclose(fp); return 0; }
	while (c != '\n'){
	    index=0;

	    if (!(c=='-' || (c >= '0' && c <= '9'))) {
		fclose(fp); return 0; }

	    while (c=='-' || (c >= '0' && c <= '9')){
		field[index++]=c;
		c=fgetc(fp);
	    }
	    field[index] = 0;
	    lit = atoi(field);
	    var = abs_val(lit);
	    if (var > nvars) nvars = var;
	    nlits ++;
	    while (space_or_paren(c)) c=getc(fp);
	    if (c==EOF){
		fclose(fp); return 0;
	    }
	}
	c=getc(fp);
	while (space_or_paren(c)) c=getc(fp);
    }
    fclose(fp);

    printf("nvars = %d\nnclauses = %d\nnlits = %d\n", nvars, nclauses, nlits);    
    allocate_memory();

    /* Second scan, to fill in the wff array */
    fp = fopen(wff_file, "r");
    c = ' ';
    wffindex = 1;
    while (white(c)) c=getc(fp);
    clause_number = 0;
    while (c != EOF && c != '%'){
	clause_number++;
	clause_start = wffindex++;
	clause_length = 0;
	if (c==EOF){
	    return  0;
	}
	tautologous_clause = 0;
	while (c != '\n'){
	    index=0;
	    while(c=='-' || (c >= '0' && c <= '9')){
		field[index++]=c;
		c=fgetc(fp);
	    }
	    field[index] = 0;
	    lit = atoi(field);

	    /* DEBUG(printf("read %s=%d ", field, lit)); */

	    repeated_literal = 0;
	    if (! tautologous_clause){
		for (i=1; i<= clause_length; i++){
		    if (lit == wff[wffindex - i].lit) {
			repeated_literal = 1;
			printf("Warning!  Repeated literal %d in clause %d\n",
			       lit, clause_number);
		    }
		    if (lit == -wff[wffindex - i].lit) {
			tautologous_clause = 1;
			wffindex = clause_start;
			nclauses--;
			printf("Warning!  Complementary literals %d and %d in clause %d\n",
			       lit, -lit, clause_number);
		    }
		}
	    }

	    if (! tautologous_clause && ! repeated_literal){
		wff[wffindex].lit = lit;
		wff[wffindex].next = -1;
		wffindex++;
		clause_length++;
	    }

	    while (space_or_paren(c)) c=getc(fp);
	    if (c==EOF){
		fclose(fp); return 0;
	    }
	}
	if (! tautologous_clause){
	    wff[clause_start].lit = clause_length;
	    wff[clause_start].next = -1;
	}

	if (clause_length == 0){
	    printf("Warning!  Wff contains empty (FALSE) clauses, and must be unsat!\n");
	}

	/* DEBUG(print_clause(clause_start)); */

	c=getc(fp);
	while (space_or_paren(c)) c=getc(fp);
    }
    fclose(fp);
    flag_format = FLAG_FORMAT_F;
    return 1;
}


int
read_in_f_lisp_format()	
{
    FILE *fp;
    int c;
    char field[MAXLINE];
    int index, wffindex, clause_start, clause_length;
    int lit, var;
    int i, tautologous_clause, repeated_literal;
    int clause_number;
    
    nvars = 0;
    nclauses = 0;
    nlits = 0;

    printf("Trying to read f-lisp-format\n");

    /* Scan once to calculate nvars, nlits, nclauses */
    if ((fp = fopen(wff_file, "r"))==NULL){
	sprintf(ss, "ERROR: cannot open wff file %s\n", wff_file);
	crash_and_burn(ss);
    }
    c = ' ';
    while (white(c)) c=getc(fp);
    while (c != EOF && c != '%'){
	if (c != '('){
	    fclose(fp); return 0;
	}
	nclauses ++;
	c=getc(fp);
	while (white(c)) c=getc(fp);
	if (c==EOF){
	    fclose(fp); return 0;
	}
	while (c != ')'){
	    index=0;

	    if (!(c=='-' || (c >= '0' && c <= '9'))){
		fclose(fp); return 0;
	    }
	    while (c=='-' || (c >= '0' && c <= '9')){
		field[index++]=c;
		c=fgetc(fp);
	    }
	    field[index] = 0;
	    lit = atoi(field);
	    var = abs_val(lit);
	    if (var > nvars) nvars = var;
	    nlits ++;
	    while (white(c)) c=getc(fp);
	    if (c==EOF){
		fclose(fp); return 0;
	    }
	}
	c=getc(fp);
	while (white(c)) c=getc(fp);
    }
    fclose(fp);

    printf("nvars = %d\nnclauses = %d\nnlits = %d\n", nvars, nclauses, nlits);    
    allocate_memory();

    /* Second scan, to fill in the wff array */
    fp = fopen(wff_file, "r");
    c = ' ';
    wffindex = 1;
    while (white(c)) c=getc(fp);
    clause_number = 0;
    while (c != EOF && c != '%'){
	if (c != '('){
	    fclose(fp); return 0;
	}
	clause_number++;
	clause_start = wffindex++;
	clause_length = 0;
	c=getc(fp);
	while (white(c)) c=getc(fp);
	if (c==EOF){
	    fclose(fp); return 0;
	}
	tautologous_clause = 0;
	while (c != ')'){
	    index=0;
	    while(c=='-' || (c >= '0' && c <= '9')){
		field[index++]=c;
		c=fgetc(fp);
	    }
	    field[index] = 0;
	    lit = atoi(field);

	    /* DEBUG(printf("read %s=%d ", field, lit)); */

	    repeated_literal = 0;
	    if (! tautologous_clause){
		for (i=1; i<= clause_length; i++){
		    if (lit == wff[wffindex - i].lit) {
			repeated_literal = 1;
			printf("Warning!  Repeated literal %d in clause %d\n",
			       lit, clause_number);
		    }
		    if (lit == -wff[wffindex - i].lit) {
			tautologous_clause = 1;
			wffindex = clause_start;
			nclauses--;
			printf("Warning!  Complementary literals %d and %d in clause %d\n",
			       lit, -lit, clause_number);
		    }
		}
	    }

	    if (! tautologous_clause && ! repeated_literal){
		wff[wffindex].lit = lit;
		wff[wffindex].next = -1;
		wffindex++;
		clause_length++;
	    }
	    
	    while (white(c)) c=getc(fp);
	    if (c==EOF){
		fclose(fp); return 0;
	    }
	}
	if (! tautologous_clause){
	    wff[clause_start].lit = clause_length;
	    wff[clause_start].next = -1;
	}
	
	/* DEBUG(print_clause(clause_start)); */

	c=getc(fp);
	while (white(c)) c=getc(fp);
    }
    fclose(fp);
    flag_format = FLAG_FORMAT_F;
    return 1;
}

int
read_in_kf_format()
{
    int i, j, len_clause, lit;
    FILE * fp;
    int tautologous_clause, repeated_literal;
    int clause_number, number_input_clauses;
    int wffstart, wffindex;

    printf("Trying to read kf-format\n");

    if ((fp = fopen(wff_file, "r"))==NULL){
	sprintf(ss, "ERROR: cannot open wff file %s\n", wff_file);
	crash_and_burn(ss);
    }

    if (fscanf(fp,"%d %d", &nvars, &nclauses ) != 2) {
	fclose(fp);
	return 0;
    }

    if (nvars <= 0){
	fclose(fp);
	return 0;
    }

    number_input_clauses = nclauses;

    /* determine number of lits in wff */
    nlits = 0;
    for (i = 1; i <= nclauses ; i++) {
	if (fscanf(fp, "%d", &len_clause)!=1){
	    printf("WARNING!  Unexpected character in file; maybe this is np format?\n");
	    fclose(fp);
	    return 0;
	}
	if (len_clause < 0) {
	    fclose(fp);
	    return 0;
	}
	nlits = nlits + len_clause;
	for (j = 1; j <= len_clause ; j++){
	    if (fscanf(fp, "%d", &lit)!=1){
		fclose(fp);
		return 0;
	    }
	}
    }
    if (fscanf(fp, "%d", &len_clause)==1) {
	fclose(fp);
	return 0;
    }
    fclose(fp);
    printf("nvars = %d\nnclauses = %d\nnlits = %d\n", nvars, nclauses, nlits);    
    allocate_memory();

    /* read in wff into .lit field, setting .next field to -1 */
    fp = fopen(wff_file, "r");
    fscanf(fp,"%d %d", &i, &i);
    wffindex = 1;
    for (clause_number=1; clause_number<=number_input_clauses; clause_number++){
	tautologous_clause = 0;
	fscanf(fp,"%d", &len_clause);
	wffstart = wffindex;
	wff[wffstart].lit = len_clause;
	wff[wffstart].next = -1;
	wffindex++;
	
	for (j=1; j<=len_clause; j++){
	    repeated_literal = 0;	
	    fscanf(fp, "%d", &lit);
	    if (! tautologous_clause){
		for (i=wffstart+1; i<wffindex; i++){
		    if (lit == wff[i].lit) {
			repeated_literal = 1;
			wff[wffstart].lit --;
			printf("Warning!  Repeated literal %d in clause %d\n",
			       lit, clause_number);
		    }
		    if (lit == -wff[i].lit) {
			tautologous_clause = 1;
			nclauses--;
			wffindex = wffstart;
			printf("Warning!  Complementary literals %d and %d in clause %d\n",
			       lit, -lit, clause_number);
		    }
		}
	    }
	    if (! tautologous_clause && ! repeated_literal){
		wff[wffindex].lit = lit;
		wff[wffindex].next = -1;
		wffindex++;
	    }
	}
    }

    fclose(fp);
    flag_format = FLAG_FORMAT_KF;
    return 1;
}
//读CNF格式文件
int
read_in_cnf_format()
{
    int i, j, len_clause, lit;//lit是literal逐字的
    FILE * fp;
    int tautologous_clause, repeated_literal;
    int clause_number, number_input_clauses;
    int wffstart, wffindex;
    int lastc;
    int nextc;

    printf("Trying to read cnf-format\n");

    if ((fp = fopen(wff_file, "r"))==NULL){//fp是一个指向打开文件的指针
	sprintf(ss, "ERROR: cannot open wff file %s\n", wff_file);
	crash_and_burn(ss);
    }
    //每调用一次fgetc(fp)其FILE * fp就会指向文件流中的下一个字符，
    //所以下面两个while是读完cnf里的全部开头的注释
    while ((lastc = fgetc(fp)) == 'c')
      {
	  while ((nextc = fgetc(fp)) != EOF && nextc != '\n');
      }//读完注释
    ungetc(lastc,fp);//int ungetc ( int character, FILE * stream );让FILE * fp指针向前退一位并将其所替换为了character，
                     //例如@#此时fp在@，fgetc之后fp在#其实这时@已经从流里消失了，ungetc('@',fp)则会变回开始状态：@# fp在@，
                     //ungetc('#',fp)则会变成## fp在第一个#
                     //对于本例由于在退出while前fgetc(fp)了一下，所以要还原ungetc(lastc,fp)

    if (fscanf(fp, "p cnf %i %i",&nvars,&nclauses) != 2){//与sscanf的区别就是:
                            //int fscanf ( FILE * stream, const char * format, ... );从文件流中按格式输入到...
                            //int sscanf ( char * str, const char * format, ...);从字符串流中按格式输入到...
	fclose(fp);
	return 0;
    }

    if (nvars <= 0){
	fclose(fp);
	return 0;
    }
	//记录子句数量
    number_input_clauses = nclauses;
    /* determine number of lits in wff */
    nlits = 0;
    for (i = 1; i <= nclauses ; i++) {//扫描所有的子句，nlits是总变量数=3*子句数
	if (fscanf(fp, "%d", &lit)!=1) { fclose(fp); return 0; }
	while (lit){//一条子句由0结尾，所以读到一条子句结尾时才能跳出while循环,所有子句读完才跳出for
	    nlits++;
	    if (fscanf(fp, "%d", &lit)!=1) { fclose(fp); return 0; }
	}
    }
    if (fscanf(fp, "%d", &len_clause)==1) {//此时fp应该是指向'%'？而len_clause应该是0？
	fclose(fp);
	return 0;
    }
    fclose(fp);
    printf("nvars = %d\nnclauses = %d\nnlits = %d\n", nvars, nclauses, nlits);    
    allocate_memory();//见“allocate_memory说明”

	/* read in wff into .lit field, setting .next field to -1 */
    fp = fopen(wff_file, "r");
    while ((lastc = fgetc(fp)) == 'c')//读注释
      {
	  while ((nextc = fgetc(fp)) != EOF && nextc != '\n');
      }
    ungetc(lastc,fp);
	//读注释
    if (fscanf(fp, "p cnf %i %i",&nvars,&nclauses) != 2){
	fclose(fp);
	return 0;
    }

    wffindex = 1;
    // 第一次读时只会执行到while里的第二个大if，完成的任务是使wff数组的lit依次存放本子句字母（变量）数，然后依次放本子句各字母变量，然后下一条子句同样。所以wff的大小是nvars+nclause+1
    for (clause_number=1; clause_number<=number_input_clauses; clause_number++){
	tautologous_clause = 0;
	wffstart = wffindex;
	len_clause = 0;
	wff[wffstart].next = -1;
	wffindex++;
	fscanf(fp, "%d", &lit);
	while (lit) {
	    repeated_literal = 0;	
	    if (! tautologous_clause){
		for (i=wffstart+1; i<wffindex; i++){
		    if (lit == wff[i].lit) {
			repeated_literal = 1;
			printf("Warning!  Repeated literal %d in clause %d\n",
			       lit, clause_number);
		    }
		    if (lit == -wff[i].lit) {
			tautologous_clause = 1;
			nclauses--;
			wffindex = wffstart;
			printf("Warning!  Complementary literals %d and %d in clause %d\n",
			       lit, -lit, clause_number);
		    }
		}
	    }
	    if (! tautologous_clause && ! repeated_literal){
		wff[wffindex].lit = lit;
		wff[wffindex].next = -1;
		wffindex++;
		len_clause++;
	    }
	    fscanf(fp, "%d", &lit);
	}
	wff[wffstart].lit = len_clause;
    }

    fclose(fp);
    flag_format = FLAG_FORMAT_CNF;
    return 1;
}

//这个函数基本不用看就是判断输入的是哪种文件就调相应文件的函数，cnf调read_in_cnf_format
void
read_in()
{
//判断wff文件是哪种文件，现在一般是.cnf
    if (flag_format == 0){
	if (0==strcmp(".f", &(wff_file[strlen(wff_file)-2])))
	  flag_format = FLAG_FORMAT_F;
	else if (0==strcmp(".np", &(wff_file[strlen(wff_file)-3])))
	  flag_format = FLAG_FORMAT_F;
	else if (0==strcmp(".lisp", &(wff_file[strlen(wff_file)-5])))
	  flag_format = FLAG_FORMAT_LISP;
	else if (0==strcmp(".kf", &(wff_file[strlen(wff_file)-3])))
	  flag_format = FLAG_FORMAT_KF;
	else if (0==strcmp(".cnf", &(wff_file[strlen(wff_file)-4])))
	  flag_format = FLAG_FORMAT_CNF;//gsat.h中
    }
    
    switch (flag_format){
      case FLAG_FORMAT_KF:
	read_in_kf_format() ||  crash_and_burn("Bad input file!\n");
	break;
      case FLAG_FORMAT_LISP:
	read_in_f_lisp_format() ||  crash_and_burn("Bad input file!\n");
	break;
      case FLAG_FORMAT_CNF:
	read_in_cnf_format() ||  crash_and_burn("Bad input file!\n");
	break;
      case FLAG_FORMAT_F:
	read_in_f_lisp_format() ||  
	  read_in_f_format() ||  
	    crash_and_burn("Bad input file!\n");
	break;
      default:
	read_in_cnf_format() ||  
	  read_in_f_lisp_format() ||  
	    read_in_kf_format() ||  
	      read_in_f_format() ||  
		crash_and_burn("Bad input file!\n");
	break;
    }
}


void
clear_out_lists()
{
    int i;
    var_str_ptr var_ptr;

    for (i = 0, var_ptr=assign; i <= nvars; i++, var_ptr++){
	var_ptr->up.list = 0;
	var_ptr->up.pos = 0;
	var_ptr->down.list = 0;
	var_ptr->down.pos = 0;
	var_ptr->sideways.list = 0;
	var_ptr->sideways.pos = 0;
	var_ptr->maxdiff.list = 0;
	var_ptr->maxdiff.pos = 0;
	var_ptr->tabu.list = 0;
	var_ptr->tabu.pos = 0;
	var_ptr->walk.list = 0;
	var_ptr->walk.pos = 0;
	var_ptr->free.list = 0;
	var_ptr->free.pos = 0;
	var_ptr->diff = 0;
	var_ptr->make = 0;
    }
}


void
init_pointers()
{
    int i, j, len_clause, alit, clause_index;
    var_str_ptr var_ptr;
    wff_str_ptr wff_ptr;

    /* initialize bad clause count array */
    for (i = 0; i <= LENGTH_BAD_CLAUSE_COUNT; i++)//LENGTH_BAD_CLAUSE_COUNT=100
      bad_clause_count[i].value = 0;

    /* initialize assign */
    clear_out_lists();
    for (i = 0, var_ptr=assign; i <= nvars; i++, var_ptr++){
	var_ptr->name = i;
	var_ptr->value = -1;
	var_ptr->value_best = 0;
	var_ptr->first= -1;
	var_ptr->prev_low = 0;
	var_ptr->positive_count = 0;
	var_ptr->flip_count = 0;
	var_ptr->pos_first = 0;
    }

    /* Initialize the next field in wff, previously */
    /* set to all -1, and the first field in assign */
	//assign[alit].first是指的从下往上扫变量alit第一次出现时的行（行号又是以该行首字母的正序号，如正序第二行的行号是5）
	//wff_ptr的next是下一条包含这个变量lit的子句序号(就是上面说的行号，以子句首的字母编号为准，如第二行是5.下一条是指的从下往上扫，即逆序)
    wff_ptr = &wff[1];
    clause_index = 1;
    for (i=1; i<=nclauses; i++) {
	len_clause = wff_ptr->lit;
	wff_ptr->pos = 0;
	wff_ptr++;

	for (j=1; j<=len_clause; j++) {
	    alit = abs_val(wff_ptr->lit);
	    wff_ptr->next = assign[alit].first;
		wff_ptr->pos = assign[alit].pos_first;
	    assign[alit].first = clause_index;
		assign[alit].pos_first = j;
	    wff_ptr ++;
	}
	clause_index += len_clause + 1;
    }

    /* Allocate and initialize clause_index_to_num, but only if it is needed 基本gsat没用*/
    if ((flag_trace & FLAG_TRACE_CLAUSE_STATE)||flag_graphics){
	clause_index_to_num = (int *) malloc((size_t)((nlits + nclauses + 1) * (sizeof(int))));
	clause_num_to_index = (int *) malloc((size_t)((nclauses + 1) * (sizeof(int))));
	for (i=1; i <= nlits + nclauses; i++) clause_index_to_num[i] = 0;
	clause_index = 1;
	for (i=1; i<=nclauses; i++) {
	    clause_index_to_num[clause_index] = i;
	    clause_num_to_index[i] = clause_index;

	    if (flag_trace & FLAG_TRACE_CLAUSES && i <= MAX_DIAGNOSTICS)
	      printf("SETTING clause_index_to_num[%d] = %d\n", clause_index, i);

	    clause_index += wff[clause_index].lit + 1;
	}
    }
}

void
reset_weights()//将wff[]中每条子句开头那个wff_str的next置1
     /* Initialize clause weights to 1 */
{
    wff_str_ptr wff_ptr;    
    int i;

    wff_ptr = &wff[1];
    for (i=1; i<=nclauses; i++) {
	wff_ptr->next = 1;
	wff_ptr += wff_ptr->lit + 1;
    }
}

/*************************************/
/*  Creating the Initial Assignment  */
/*************************************/


void
read_initial_assign()
{
    int i;
    FILE * infile;
    int lit;

    if (!flag_partial)
      for (i = 1; i <= nvars; i++){
	  assign[i].value = -1;
	  if (flag_graphics) graphics_show_variable(i, 0);
      }
    else {
	for (i = 1; i <= nvars; i++){
	    assign[i].value = random_01_odds(odds_true) ? 1 : -1;
	    if (flag_graphics) graphics_show_variable(i, 0);
	}
    }
    if ((infile = fopen(init_file, "r")) == NULL){
	sprintf(ss, "Cannot open %s\n", init_file);
	crash_and_burn(ss);
    }
    i=0;
    while (fscanf(infile, " %d", &lit)==1){
	i++;
	if (abs(lit)>nvars){
	    sprintf(ss, "Bad init file %s\n", init_file);
	    crash_and_burn(ss);
	}
	if (lit<0) assign[-lit].value= -1;
	else assign[lit].value =1;
	if (flag_graphics) graphics_show_variable(abs(lit), 0);
    }
    if (i==0){
	sprintf(ss, "Bad init file %s\n", init_file);
	crash_and_burn(ss);
    }
    close(infile);
}




void
init_assign_values_randomly()//随机初始化assign[].value & first_init_value
     /* initializes assign values randomly */
{
    int i;
    var_str_ptr iptr;

    iptr = &assign[1];
    for (i = 1; i <= nvars; i++){
	if (flag_fixed_init && current_try > 1){//flag_fixed_init=0跳过
	    iptr->value = iptr->first_init_value;
	}
	else {
	    if ( random_01_odds(odds_true) )//random_01_odds返回值01随机，所以实现每一个变量的随机赋值
	      iptr->value = 1; 
	    else
	      iptr->value = -1;
	}
	if (current_try == 1) iptr->first_init_value = iptr->value;
	if (flag_graphics) graphics_show_variable(i, 0);
	iptr ++;
    }
}

int
force_vars(PROTO(int) chainvar, PROTO(int) clause)	
     /* Perform unit propagation, */
     /* setting forced variable in clause if any. */
     /* Returns next clause containing chainvar. */
PARAMS(int chainvar; int clause;)
{
    int i, var, undetermined, literal, satisfied, len, next_clause;
    undetermined = 0;
    satisfied = 0;
    len = wff[clause].lit;
    next_clause = 0;

    /* DEBUG(printf("force vars( chainvar=%d, clause=%d )\n", chainvar, clause)); */
    /* DEBUG(print_clause(clause)); */

    for (i = 1; i <= len; i++) {
	var = abs_val(wff[clause+i].lit);
	if (var == chainvar) {
	    next_clause = wff[clause+i].next;
	}
	if (satisfied==0) {
	    if (assign[var].value == -2) {
		if (undetermined != 0) {
		    satisfied = 1;
		}
		else {
		    undetermined = var;
		    literal = wff[clause+i].lit;
		}
	    }
	    else if ((assign[var].value * wff[clause+i].lit) > 0 ) {
		satisfied = 1;
	    }
	}
    }
    if ((satisfied == 0) && (undetermined != 0)) {
        if (literal > 0)
	  assign[undetermined].value = 1;
        else
	  assign[undetermined].value = -1;
	propagate_from(undetermined);
    }
    if (next_clause == 0) {
	crash_and_burn("ERROR! bad next_clause in force_vars!\n");
    }
    return next_clause;
}

void
propagate_from( PROTO(int) var)
     /* Added by Kautz -- earlier version did not */
     /* chain unit propagations! */
PARAMS( int var; )
{
    int clause;
    var_str_ptr varptr;

    if (flag_graphics) graphics_show_variable(var, 0);
    varptr = &assign[var];
    delete_from(free, varptr);
    clause = assign[var].first;
    while (clause != -1) {
	clause = force_vars(var, clause);
    }
}

void
init_assign_values_prop() 
     /* init assigns values randomly with propagation */
{
    int i, var;
    
    /* Put all variables in the free list */
    for (i = 1; i <= nvars; i++){
	assign[i].value = -2;
	assign[i].free.list = i;
	assign[i].free.pos = i;
    }
    length_of(free) = nvars;

    /* Give a random value to each free variable and propagate */
    while (length_of(free) != 0) {
	var = random_member(free);
	CHECK({
	    if ((var == 0) || (assign[var].value != -2)) { crash_and_burn("Init assign error\n"); }
	});
	if ( random_01_odds(odds_true) )
	  assign[var].value = 1;
	else
	  assign[var].value = -1;
	propagate_from(var);
    }
}

void
init_assign_values() //随机初始化了assign[].value & first_init_value & value_low & pre_low值都一样
     /* assigns new values randomly from rand_ass */
{
    int i, count_ident, prev;
    var_str_ptr var_ptr;

    if (flag_trace & FLAG_TRACE_CLAUSE_STATE)
      printf("START initial assignment\n");

    clear_out_lists();

    /*  every reset_tries steps completely randomize  */ 
    if ( (try_this_assign - 1) % reset_tries == 0){
	if (init_file[0])//初始为0跳过
	  read_initial_assign();
	else if (flag_init_prop == 1)//初始为0跳过
	  init_assign_values_prop();
	else 
	  init_assign_values_randomly();//初始时执行了的,给每一个变量随机地赋值（1真-1假）,assign[].value & first_init_value

	for (i = 1, var_ptr = &assign[1]; i <= nvars; i++, var_ptr++){
	    var_ptr->value_low = var_ptr->prev_low = var_ptr->value;//value是上面函数中，每一个变量的随机真值
	}
	if (flag_trace && reset_tries != 1) printf("Resetting averaging\n");//初始未打印
	return; 
    }

    if (flag_adaptive){//未调用
	/* Compute initial states by "adaptive random starts" -- 
	   use values from previous lowest state, and make this number
	   of random flips.  */
	var_ptr = &assign[1];
	for (i = 1; i <= nvars; i++){
	    var_ptr->value = var_ptr->value_low;
	    var_ptr++;
	}
	for (i=1; i<=flag_adaptive; i++){
	    assign[random_1_to(nvars)].value *= -1;
	}
    }
    else{
	/* Create starting assignment by averaging the lowest assignments */
	/* from the preceeding two tries */
	count_ident = 0;
	var_ptr = &assign[1];
	for (i = 1; i <= nvars; i++){
	    prev = var_ptr->prev_low;
	    var_ptr->prev_low =  var_ptr->value_low; /* Used to be just "value" */
	    if (prev == var_ptr->value_low){
		count_ident++;
		var_ptr->value = prev;
	    }
	    else {
		var_ptr->value = ( random_01_odds( INT_PROB_BASE/2 ) ? 1 : -1 );
	    }
	    if (flag_graphics) graphics_show_variable(i, 0);
	    var_ptr++;
	}
    if (flag_trace & FLAG_TRACE_CLAUSES) {printf("count_ident:      %d\n", count_ident);}
    }
}


/*************************************/
/*  Managing Tabu List               */
/*************************************/

void
init_tabu()
{
    tabu_in = 0;
    tabu_out = 0;
}

void
rotate_tabu_list( PROTO(int) var )
PARAMS( int var; )
{
    var_str_ptr varptr;
    int outvar;

    /* Put var into tabu list, and remove oldest member from tabu list.  */
    if (tabu_list_length > 0){//由于没启用tabu搜索，所以跳过到最后
	if (flip > tabu_list_length){
	    if (++tabu_out > tabu_list_length)
	      tabu_out = 1;
	    outvar = assign[tabu_out].tabu.list;
	    CHECK({
		if (outvar < 1 || outvar > nvars){
		    sprintf(ss, "Bad variable %d appears in tabu list position %d\n",
			    outvar, tabu_out);
		    crash_and_burn(ss);
		}
	    });
	    varptr = &assign[outvar];
	    varptr->tabu.pos = 0;
	    adjust_bucket(varptr);
	}
	if (++tabu_in > tabu_list_length)
	  tabu_in = 1;
	assign[tabu_in].tabu.list = var;
	varptr = &assign[var];
	varptr->tabu.pos = tabu_in;
	if (flag_hillclimb){
	    delete_if_in(up, varptr);
	    delete_if_in(down, varptr);
	    delete_if_in(sideways, varptr);
	}
	else {
	    delete_if_in(maxdiff, varptr);
	}
	delete_if_in(walk, varptr);
    }
}

void
print_tabu_list()
{
  int len, i, j;

  len = (flip < tabu_list_length) ? flip : tabu_list_length;
  printf("Tabu list: ");

  j = tabu_out;
  for (i=1; i<=len; i++){
      if (++j > tabu_list_length)
	j = 1;
      printf(" %d ", assign[j].tabu.list);
  }
  printf("\n");
}


/*************************************/
/*  Flipping and Calculating Diffs   */
/*************************************/

#define SCALED_WEIGHT  (flag_weigh_clauses ? weight : 1)


int
pick_greedy_var()
{
    if (flag_hillclimb){
	return length_of(down) ? random_member(down) 
	  : ( length_of(sideways) ? random_member(sideways)
	     : random_member(up) );
    }
    else {
	return random_member(maxdiff);//是宏：assign[random_1_to(length_of(maxdiff))].maxdiff.list; 而length_of又是宏：assign->maxdiff.list
    }
}

int
plateau_pick_var()
{
    int i;

    if (flag_plateau > current_num_bad){
	printf("Overshot plateau!\n");
	return 0;
    }
    if (flag_hole) {
	if (flag_hole_continue) {
	    print_assign_stdout();
	    for (i=1; i<=length_of(down); i++)
	      printf("Hole: %d\n", assign[i].down.list);
	}
	if (flips_to_plateau == 0) {
	    flips_to_plateau = flip;
	    flip = 0;
	}
	if (length_of(down)) {
	    printf("Plateau length: %d %d\n", flip + 1, flips_to_plateau);
	    if (flag_hole_continue)
	      flag_hole = 0;
	    else
	      return 0;
	}
	if (flip + 1 == max_flips)
	  printf("Partial length: %d %d\n", flip + 1, flips_to_plateau);
    }
    else {
	print_assign_stdout();
	for (i=1; i<=length_of(down); i++)
	  printf("Hole: %d\n", assign[i].down.list);
    }
    if (length_of(sideways)) 
      return random_member(sideways);
    else
      return 0;
}

int 
pick_rand_var()//如果是basic gsat则什么if都调用不到，直接到最后一句 
{
    int var, i;

    if (flag_trace & FLAG_TRACE_DIFFS){
	if (flag_hillclimb){
	    print_list(down, diff, "DOWN: Vars with diff>0 : ");
	    print_list(sideways, diff, "SIDEWAYS: Vars with diff=0 : ");
	    print_list(up, diff, "UP: Vars with diff<0 : ");
	}
	else {
	    print_list(maxdiff, diff, "MAXDIFF: Vars with max diff: ");
	}
    }
    if (flag_trace & FLAG_TRACE_MAKES)
      print_list(walk, make, "WALK: Vars with make>0 : ");
    if (flag_trace & FLAG_TRACE_TABU)
      print_tabu_list();

    if (flag_manual_pick){
	printf(">>>> For flip %d, I should pick : ", flip + 1);
	scanf("%d", &var);
	if (var) return var;
    }

    if (flag_anneal)
      return (anneal_pick_var());

    if ((flag_plateau) && (flag_plateau >= current_num_bad)) 
      return plateau_pick_var();
      
    if (flag_walk){
	if ((flag_walk < 0 && random_01_odds(-flag_walk))
	    ||
	    (flag_walk > 0 && current_max_diff <= 0 && random_01_odds(flag_walk))){
	    if (flag_walk_all_vars || length_of(walk) == 0)
	      var = random_1_to(nvars);
	    else
	      var = random_member(walk);
	    if (flag_trace & FLAG_TRACE_WALKS)
	      printf("Walk var=%d, diff=%d, make=%d\n", var, assign[var].diff, assign[var].make);
	    return var;
	}
    }

    return pick_greedy_var();
}


void
init_buckets()
{
    var_str_ptr varptr;
    int i;
    int md, bl;

    if (flag_hillclimb){
	for (i=1, varptr = &assign[1]; i<=nvars; i++, varptr++){
	    /* vars that appear in no clause should never be flipped,
	       so don't put them in any bucket */
	    if (!is_in(tabu, varptr) && 
		(!flag_only_unsat || varptr->make > 0) &&
		(varptr->first != -1 || flag_coloring)){
		adjust_bucket(varptr);
	    }
	}
    }
    else {
	md = -BIG;//md的意思是maxdiff存储所有变量中最大的maxdiff
	bl = 0;//buckets length的意思？
	for (i=1, varptr = &assign[1]; i<=nvars; i++, varptr++){
	    if (!is_in(tabu, varptr) &&//is_in是宏：varptr->tabu.pos 
		(!flag_only_unsat || varptr->make > 0) &&
		(varptr->first != -1 || flag_coloring)){//varptr->first != -1的意思是该字母在CNF中出现不止一次。为什么要专门列出来？
		if (varptr->diff > md){
		    bl = 1;
		    assign[1].maxdiff.list = varptr->name;//将有最大diff的字母记录在assign[1].maxdiff.list中，并且每次遇到最大diff的字母时都将bl重新置1,以便用于下面的else if中，所以assgn[1,2...bl].maxdiff.list是记录的拥有最大diff的字母列表
		    md = varptr->diff;
		}
		else if (varptr->diff == md){
		    assign[++bl].maxdiff.list = varptr->name;
		}
		if (varptr->make > 0 && !is_in(walk, varptr)){//is_in:varptr->walk.pos
		    add_to(walk, varptr);//add_to是宏：assign[varptr->walk.pos = ++(assign->walk.list)].walk.list = (varptr ->name);所以assign[1,2...make>0的字母个数(即assign[1].walk.list的值)].walk.list记录的是make>0的字母的列表.该字母varptr的walk.pos记录该字母出现在assign[1].walk.list的位置，即是第几个make>0的字母
		}
	    }
	}
	for (i=1, varptr = &assign[1]; i<=bl; i++, varptr++){
	    assign[ varptr->maxdiff.list ].maxdiff.pos = i;
	}
	assign->maxdiff.list = bl;
	current_max_diff = md;
    }
}



void
init_diff()
     /* Initializes assign.diff, assuming it has previously be set to 0 */
{
    int i, clause_len, j;
    register wff_str_ptr clause_ptr, inner_clause_ptr;
    wff_str_ptr clause_start;
    var_str_ptr alit_ptr;
    int lit, pot_crit, npos, alit;
    int clause_index;
    int weight;
    int offset;
    int notice_clause_state;
	int pos;

    notice_clause_state = ((flag_trace & FLAG_TRACE_CLAUSE_STATE)||flag_graphics);

    /* printf("Initializing diff\n"); */

    for (offset=0; (offset==0) || (offset < flag_coloring); offset++){

	if (flag_trace & FLAG_TRACE_DIFFS){//FLAG_TRACE_DIFFS=4
	    printf("Initializing diffs, offset=%d\n", offset);
	}
	clause_index = 1;
	clause_start = &wff[1];
	for (i = 1; i <= nclauses; i++) {
	    clause_ptr = clause_start;
	    clause_len = clause_start->lit;
	    weight = flag_weigh_clauses ? clause_start->next : 1;
	    
	    clause_ptr++;
	    
	    if ((offset == 0) || (clause_ptr->lit < 0)) { /* Only use offsets on negative clauses */

		/* printf("init: offset=%d, clause index=%d, clause= ", offset, clause_index); */
		/* print_offset_clause(clause_index, offset); */

		npos = 0;
		for (j = 1; j <= clause_len; j++){//扫描所有子句，将字母的真值带入看是否满足
		    lit = clause_ptr->lit;
		    alit = abs_val(lit) + offset;
		    if ((assign[alit].value * lit) > 0) {
			npos++;//记录该子句中随机赋值后为正的字母数
			pot_crit = alit;//记录该子句中最后一个赋值后为正的字母
			pos = j;
		    }
		    clause_ptr++;
		}

		/* printf("npos: %d\n", npos); */

		if (notice_clause_state) {
		    trace_clause_state(clause_index, (npos > 0) ? 1 : -1);
		}
		//当子句中只有一个字母为真两个为假时npos==1，对这个字母的diff-1，因为如果该字母flip后总体的不满足子句将增加一个（其所在子句将不满足）同理如果该字母在其他子句中也有同样地位的话将再diff-1
		if (npos == 1) { /* pot_crit is critical */
		    assign[pot_crit].diff -= weight;
			clause_start->pos = pos;
		}
		else if (npos == 0) { /* clause is unsat */
		    inner_clause_ptr = clause_start + 1;//如果该子句不满足就将操作指针重新指向该子句首，用weight来改变该子句中每一个字母的diff和make值,diff:因为该子句中任何一个字母flip都将使总体的满足数+1，因此diff+1，make:表示当前子句不满足但该字母flip后将满足，该字母这样有效的子句数。
		    for (j = 1 ; j <= clause_len ; j++) {
				alit = abs_val(inner_clause_ptr->lit) + offset;
				alit_ptr = &assign[alit];
				alit_ptr->diff += weight;
				alit_ptr->make += weight; /* Add to pos make list */
				inner_clause_ptr++;
		    }
		}
		clause_start->next = npos;
	    }
	    clause_index += clause_len + 1;
	    clause_start += clause_len + 1;
	}
    }
    if (flag_trace & FLAG_TRACE_CLAUSE_STATE)
      printf("END initial assignment\n");
}


void
update_diff(PROTO(int) var)
     /* Update diffs for var, including implicit clauses */
PARAMS(int var;)
{
    wff_str_ptr clause_ptr;
    wff_str_ptr clause_start;
    var_str_ptr var_ptr, other_var_ptr, alit_ptr;
    int i, lit, alit, clause_len, npos, var_makes_clause, next_clause, other_var;
    int offset;
    int weight;
    int this_clause;
    int notice_clause_state;
	int pos;

    notice_clause_state = (flag_trace & FLAG_TRACE_CLAUSE_STATE)||flag_graphics;

    var_ptr = &assign[var];
    offset = flag_coloring ? ((var - 1) % flag_coloring) : 0;
    next_clause = assign[var - offset].first;//逆扫时该字母第一次出现时所在行的行头序号
	pos = assign[var].pos_first;

    /* printf("Update var=%d offset=%d\n", var, offset); */

    while (next_clause != -1) {//要到正扫的第一个该变量
	
	clause_len = (clause_ptr = clause_start = &wff[this_clause = next_clause])->lit;//其实就是clause_len=3
	weight = flag_weigh_clauses ? clause_ptr->next : 1;//在基本gsat中weight似乎永远都是为1的
	clause_ptr++;

	/* printf("Testing clause "); */
	/* print_clause(next_clause); */

	npos = 0;//赋值后为正字母的个数
	var_makes_clause = 0;
	if (clause_start->next >= 3) {
		lit = (clause_start + pos)->lit;
		if (same_sign(assign[var].value, lit)){
			clause_start->next += 1;
		}
		else {
			clause_start->next -= 1;
		}
	}
	else if (clause_start->next == 2) {
		lit = (clause_start + pos)->lit;
		if (same_sign(assign[var].value, lit)){
			clause_start->next += 1;
		}
		else {
			clause_start->next -= 1;
			for (i = 1; i <= clause_len; i++) {
				lit = clause_ptr->lit;
				alit = abs_val(clause_ptr->lit);
	    		/* printf("Alit = %d  ", alit); */

	    		if (same_sign((alit_ptr = &assign[alit])->value, lit)){//字母是负(正)，赋值也是负(正)，即整个变量赋值后为真才能进if.npos其实就是记录赋值后为正字母的个数
 		    		other_var = alit;
 		    		other_var_ptr = alit_ptr;
					clause_start->pos = i;
					break;
				}
 	    		clause_ptr++;
			}//遍历完一个子句	    
		    /* other_var becomes critical */
		    other_var_ptr->diff -= weight;//更新这个子句的diff(初始是在init_buckets里初始化)，由于该子句有变量flip了所以其相应的diff也要更新
		    adjust_bucket(other_var_ptr);//更新maxdiff列表和walk列表，见adjust_buckets.h
		}
	}
	else if (clause_start->next == 1) {
		lit = (clause_start + pos)->lit;
		if (same_sign(assign[var].value, lit)) {
			clause_start->next += 1;
			alit = abs_val((clause_start + clause_start->pos)->lit);
			other_var_ptr = &assign[alit];
			other_var_ptr->diff += weight;
			adjust_bucket(other_var_ptr);
		}
		else {
			clause_start->next -= 1;
		    /* clause becomes unsat */
		    if (notice_clause_state)
	    	  trace_clause_state(this_clause, -1);
		    current_num_bad++;
		    clause_ptr = clause_start + 1;
		    for (i = 1 ; i <= clause_len ; i++) {
			if ((lit = clause_ptr->lit)<0)
			  alit = -lit + offset;
			else
			  alit = lit;
			(alit_ptr = &assign[alit])->diff += weight;
			alit_ptr->make += weight;
			if (alit != var) adjust_bucket(alit_ptr);
			clause_ptr++;
		    }
		    var_ptr->diff += weight;
		}
	}
	else if (clause_start->next == 0) {
		clause_start->next += 1;
	    /* clause becomes pos; reduce makes; var becomes critical */
	    if (notice_clause_state)
	      trace_clause_state(this_clause, 1);
	    current_num_bad-- ;//该子句原来为负
	    clause_ptr = clause_start + 1;//重新遍历该子句
	    for (i = 1 ; i <= clause_len ; i++) {
			if ((lit = clause_ptr->lit)<0)//if else求出变量的绝对值，即字母
			  alit = -lit + offset;
			else
			  alit = lit;
			(alit_ptr = &assign[alit])->diff -= weight;//将该子句中每一个diff-1
			alit_ptr->make -= weight;//将该子句中每一个make-1
 			if (alit != var) 
 				adjust_bucket(alit_ptr);
 			if (alit == var) 
 				clause_start->pos = i;

			clause_ptr++;
	    }
	    var_ptr->diff -= weight;//对于flip后仅有一个为真且是flip的那个字母，这个flip的字母的diff要-2
	}
	next_clause = (clause_start + pos)->next;
	pos = (clause_start + pos)->pos;
	}



// 	for (i = 1; i <= clause_len; i++) {
// 		lit = clause_ptr->lit;
// 		alit = abs_val(clause_ptr->lit);
// 	    /* printf("Alit = %d  ", alit); */
// 
// 	    if (same_sign((alit_ptr = &assign[alit])->value, lit)){//字母是负(正)，赋值也是负(正)，即整个变量赋值后为真才能进if.npos其实就是记录赋值后为正字母的个数
// // 		npos ++;
// // 		if (alit == var) {//赋值后的变量为真且是flip的那个字母
// // 		    var_makes_clause = 1;
// // 		}
// // 		else {
// // 		    other_var = alit;
// // 		    other_var_ptr = alit_ptr;
// // 		}
// // 	    }
//  	    	npos++;
// 			if (alit == var) {
// 				var_makes_clause = 1;
// 			}
// 			else if (cnpos == 1 && !var_makes_clause) {
// 				npos = cnpos;
// 				other_var = alit;
// 				other_var_ptr = alit_ptr;
// 				clause_start->pos = i;
// 				break;
// 			}
// 			else {
// 				other_var = alit;
// 				other_var_ptr = alit_ptr;
// 			}
// 		}
// 	    clause_ptr++;
// 	//遍历完一个子句
// 
// 	/* printf(" npos = %d, var_makes_clause = %d, other_var=%d \n", npos, var_makes_clause, other_var);  */
// 
// 	if ((npos == 1) && !var_makes_clause) {//子句只有一个字母赋值后值为正且不是flip的那个字母
// 	    /* other_var becomes critical */
// 	    other_var_ptr->diff -= weight;//更新这个子句的diff(初始是在init_buckets里初始化)，由于该子句有变量flip了所以其相应的diff也要更新
// 	    adjust_bucket(other_var_ptr);//更新maxdiff列表和walk列表，见adjust_buckets.h
// 	}
// 	else if ((npos == 2) && var_makes_clause){//子句有两个字母赋值后值为正且有一个是flip后的那个字母
// 	    /* other_var becomes uncritical */
// 	    other_var_ptr->diff += weight;
// 	    adjust_bucket(other_var_ptr);
// 	}
// 	else if (npos == 0){
// 	    /* clause becomes unsat */
// 	    if (notice_clause_state)
// 	      trace_clause_state(this_clause, -1);
// 	    current_num_bad++;
// 	    clause_ptr = clause_start + 1;
// 	    for (i = 1 ; i <= clause_len ; i++) {
// 		if ((lit = clause_ptr->lit)<0)
// 		  alit = -lit + offset;
// 		else
// 		  alit = lit;
// 		(alit_ptr = &assign[alit])->diff += weight;
// 		alit_ptr->make += weight;
// 		if (alit != var) adjust_bucket(alit_ptr);
// 		clause_ptr++;
// 	    }
// 	    var_ptr->diff += weight;
// 	}
// 	else if (npos == 1) {//仅有一个字母赋值后值为正且是flip的那个字母,即证明该子句原来为负
// 	    /* clause becomes pos; reduce makes; var becomes critical */
// 	    if (notice_clause_state)
// 	      trace_clause_state(this_clause, 1);
// 	    current_num_bad-- ;//该子句原来为负
// 	    clause_ptr = clause_start + 1;//重新遍历该子句
// 	    for (i = 1 ; i <= clause_len ; i++) {
// 		if ((lit = clause_ptr->lit)<0)//if else求出变量的绝对值，即字母
// 		  alit = -lit + offset;
// 		else
// 		  alit = lit;
// 		(alit_ptr = &assign[alit])->diff -= weight;//将该子句中每一个diff-1
// 
// 		alit_ptr->make -= weight;//将该子句中每一个make-1
// 		if (alit != var) adjust_bucket(alit_ptr);
// 		clause_ptr++;
// 	    }
// 	    var_ptr->diff -= weight;//对于flip后仅有一个为真且是flip的那个字母，这个flip的字母的diff要-2
// 	}
// 	else if (npos ==3) {
// 		clause_start->next = npos;
// 	}
//     
    adjust_bucket(var_ptr);//因为每一条包含flip字母的子句都会改变flip字母的状态，所以在最后adjust_bucket一下
//   for (i=0 ; i <=nvars ; i++) {
//      printf("assign[%d]: value:%d  diff:%d  make:%d  walk:%d/%d  maxdiff:%d/%d\n", i, assign[i].value, assign[i].diff, assign[i].make, assign[i].walk.pos, assign[i].walk.list, assign[i].maxdiff.pos, assign[i].maxdiff.list);
//  }
}


int
compute_max_diff()
{
    if (flag_hillclimb){
	return length_of(down) ? 1 : 
	  ( length_of(sideways) ? 0 : -1 );
    }
    else {
	if (length_of(maxdiff)==0)//length_of是宏：assign->maxdiff.list,所以是有最大diff的字母数
	  init_buckets();
	return current_max_diff;
    }
}


void
flip_var(PROTO(int) var)
     /* flip var and update make/critical/diff and max_diff_list */
PARAMS( int var; )
{  
    int diff;
    int old_num_bad;

    old_num_bad = current_num_bad;
    diff = assign[var].diff;

    if (diff < 0)//该变量flip后unsat子句数+
      ++upwards_count;
    else if (diff == 0)//flip后unsat子句数不变
      ++sideways_count;
    else //flip后unsat子句数-
      ++downwards_count;
    assign[var].flip_count++;

    if ((flag_trace & FLAG_TRACE_FLIPS)){
	printf("Flip %d: var %d to %d, diff=%d, make=%d, num_bad=%d, low_bad=%d\n", 
	       flip, var, -assign[var].value, assign[var].diff,
	       assign[var].make,
	       current_num_bad,
	       low_bad);
    }

    CHECK({//在gsat.h中定义的宏，其实就是执行下面的,由于没有启用tabu禁忌搜索，所以跳过。如何进入宏调试？
	if (is_in(tabu, (&assign[var]))){//(&assign[var]->tabu.pos)
	    sprintf(ss, "Flipping var %d, but is tabu with diff %d\n",
		    var, diff);
	    crash_and_burn(ss);
	}
	if (flag_only_unsat && assign[var].make <= 0){
	    sprintf(ss, "Flipping var %d, but it has make %d\n",
		    var, assign[var].make);
	    crash_and_burn(ss);
	}
    });

    assign[var].value *= -1;//flip了~~

    rotate_tabu_list(var);//没启用tabu搜索，所以什么都没干

    update_diff(var);

    if (flag_trace & FLAG_TRACE_FLIP_CLAUSES){
	if (get_bad_clauses(1, 0) != current_num_bad){
	    sprintf(ss, "current_num_bad=%d, but actual count is %d!\n",
		    current_num_bad, get_bad_clauses(0,0));
	    crash_and_burn(ss);
	}
    }

    if (flag_trace & FLAG_TRACE_ASSIGN)
      print_assign_stdout();

    CHECK({
	if (!flag_weigh_clauses){
	    if (current_num_bad != (old_num_bad - diff)){
		sprintf(ss, "Diff = %d, but current_num_bad changes from %d to %d!\n",
			diff, old_num_bad, current_num_bad);
		crash_and_burn(ss);
	    }
	}
    });

    if (current_num_bad < low_bad ){//low_bad存放最小的num_bad
	low_bad = current_num_bad;
	if (current_num_bad <= flag_save_best_max){
	    save_current_as_low();//存放本try中最好的取值到assign[].value_low
	}
    }

    if (current_num_bad < best_num_bad && current_num_bad <= flag_save_best_max){
	save_current_as_best();//so far最好的取值到assign[].value_best还有更新一些全局变量
    }

    if (flag_graphics) graphics_show_variable(var, 1);
#ifndef NO_USLEEP
    if (pause_usecs)
      usleep(pause_usecs);
#endif
}
/**************************************/
/*  Big Flips                         */
/**************************************/

void
big_flip()
{
    int i;
    int var;
    int flipsize;
    int pr;

    pr = !!(flag_trace & FLAG_TRACE_FLIPS);

    flipsize = length_of(walk);
    if (pr) printf("Big flip %d size %d, num_bad=%d, low_bad=%d, randomizing ", 
		   flip, flipsize, current_num_bad, low_bad);
    for (i=1; i<= length_of(walk); i++)
      assign[i].lastwalk = assign[i].walk.list;
    for (i=1; i<= flipsize; i++){
	var = assign[i].lastwalk;
	if (pr) printf(" %d", var);
	if (random_01_odds( INT_PROB_BASE/2 )){
	    if (pr) printf("*");
	    assign[var].flip_count++;
	    assign[var].value *= -1;
	    update_diff(var);
	}
    }
    if (pr) printf("\n");

    if (current_num_bad < low_bad ){
	low_bad = current_num_bad;
	if (current_num_bad <= flag_save_best_max){
	    save_current_as_low();
	}
    }

    if (current_num_bad < best_num_bad && current_num_bad <= flag_save_best_max){
	save_current_as_best();
    }

}

/**************************************/
/*  Checking for Unsatisfied Clauses  */
/**************************************/

int 
check_assign_best()
     /* returns 0 if assign_best is unsat; 1 if sat */
     /* This procedure is used as a double check, and */
     /* may be eliminated if necessary */
{
    int i, clause_len, j, clause_index;
    register wff_str_ptr clause_ptr;
    int bad;
    int offset;

    for (offset=0; (offset==0) || (offset < flag_coloring); offset++){
	clause_index = 1;
	for (i = 1; i <= nclauses; i++) {
	    clause_ptr = &wff[clause_index];
	    clause_len = clause_ptr->lit;
	    clause_ptr++;

	    if ((offset == 0) || (clause_ptr->lit < 0)) { /* Only use offsets on negative clauses */
		bad = 1;
		for (j = 1; j <= clause_len; j++){
		    if (assign[abs_val(clause_ptr->lit) + offset ].value_best * clause_ptr->lit > 0 ) {
			bad = 0;
			break;
		    }
		    clause_ptr++;
		}
		if (bad) {
		    printf("\nWFF *NOT* SATISFIED BY ASSIGN\n");
		    return 0;
		}
	    }
	    clause_index += clause_len + 1;
	}
    }
    printf("\nWFF SATISFIED BY ASSIGN\n"); 
    return 1;
}


int 
get_bad_clauses(PROTO(int) print_flag, PROTO(int) update_flag)
     /* Returns number of unsat clauses, by actually */
     /* checking all clauses.  Use to initialize */
     /* current_num_bad, for diagnositics, and to update clause weights. */
     /* If print_flag != 0, then print the list of bad clauses. */
     /* If update_flag != 0, then increment the weight of unsatisfied clauses. */
PARAMS(int print_flag; int update_flag;)
{
    int clause_len, j, num_bad, clause_index;
    wff_str_ptr clause_ptr;
    int lit, alit;
    int bad, offset, clause_number;

    if (print_flag) printf("Bad clauses:\n");
    num_bad = 0;

    for (offset=0; (offset==0) || (offset < flag_coloring); offset++){
	clause_index = 1;
	for (clause_number = 1; clause_number <= nclauses; clause_number++) {
	    clause_ptr = &wff[clause_index];
	    clause_len = clause_ptr->lit;
	    clause_ptr++;

	    if ((offset == 0) || (clause_ptr->lit < 0)) { 
		/* Only use offsets on negative clauses */
		bad = 1;
		for (j = 1; j <= clause_len; j++){
		    if ((lit = clause_ptr->lit)<0)
		      alit = -lit + offset;
		    else
		      alit = lit;
		    if (same_sign(assign[alit].value, lit)){//子句中有一个字母赋值后为真则bad=0
			bad = 0;
			break;
		    }
		    clause_ptr++;
		}
		if (bad) {//初始时一个if都没运行，其实就是num_bad计数
		    num_bad++;
		    if (current_num_bad == 1 && (flag_trace & FLAG_TRACE_ORPHANS)){
			printf("ORPHANED clause %d is ", clause_number);
			print_offset_clause(clause_index, offset);
		    }
		    if (update_flag){
			wff[clause_index].next += weight_update_amt;
		    }
		    if (print_flag && num_bad <= MAX_DIAGNOSTICS) { 
			printf("Unsat clause %d is ", clause_number);
			print_offset_clause(clause_index, offset);
		    }
		}
	    }
	    clause_index += clause_len + 1;
	}
    }
    if (print_flag) printf("Total bad clauses = %d\n", num_bad);
    return num_bad;
}



/**************************/
/*  Main Subroutines      */
/**************************/

void
main_init_experiment(PROTO(char **) argv, PROTO(int) argc)
PARAMS( char ** argv; int argc; )
{
  setbuf(stdout,NULL);//void setbuf ( FILE * stream, char * buffer );将流缓存到buffer再一起输出给stream，buffer为NULL则要求不缓存。这里的作用就是取消输出缓存，即程序运行时即时给出打印内容。

//tmpfile:Creates a temporary binary file. FILE * try_stat_filep在gsat.h中被extern，在globals.c中被定义
  if ((try_stat_filep = tmpfile()) ==  NULL)//创建了一个scratch file:a temporary computer file that is created to hold information while a program is being used.该语句创建了一个临时FILE(try_stat_filep)目前还不知道拿来做什么。
    crash_and_burn("Cannot create scratch file"); //一个log错误的函数，实现在utils.c里，没懂

  parse_parameters();//分析了用户的输入和文件名等系统信息
  read_in();//判断wff文件类型，扫描两次wff,初始时扫描一遍cnf判断有无错误并读入nlits等相关信息，第二遍扫描cnf时就是初始化wff[].lit,对next无操作
  if (max_flips<0){
      max_flips = (-max_flips)*nvars;
      printf("max_flips: %d\n", max_flips);
  }
  tabu_list_length = (tabu_list_length < nvars) ? tabu_list_length : nvars;

  if (flag_convert) {//初始为0
      output_converted_wff();
      exit(0);
  }

  if (flag_graphics)//初始为0
	 graphics_init(argv, argc);

  init_rand(); //计算随机种子   
  init_pointers();//初始化assign[]各项(置0),first置-1，wff的next和pos,alpha版增加pos_first和wff[].pos
  if (flag_trace & FLAG_TRACE_CLAUSES){//按位与,flag_trace=128,FLAG_TRACE_CLAUSES=64,所以结果为0,初始时以下两函数没调用
      print_wff();
      print_wff_clauses();
  }
  best_num_bad = BIG;//=2^31-1
  printf("Initialization Complete\n");
  //下面的信号函数不知道是干什么的?
  flag_abort = 0;
  signal(SIGINT, handle_interrupt);//void (*signal(int sig, void (*func)(int)))(int);SIGINT	(Signal Interrupt) Interactive attention signal. Generally generated by the application user.
  if(signal(SIGQUIT, SIG_IGN) != SIG_IGN)
    signal(SIGQUIT, handle_interrupt);
  signal(SIGTERM, handle_interrupt);

  experiment_seconds = 0;
  elapsed_seconds();//计算上次进程调用这个函数到这次进程调用这个函数逝去的时间,返回一个double的时间，但是没变量接这个返回值？

  total_downwards = 0;
  total_upwards = 0;
  total_sideways = 0;
  total_null = 0;
  total_num_assigns = 0;
  total_sum_flips = 0;
  total_sum_successful_flips = 0;
  total_successful_reset_count = 0;
  total_successful_flips_incl_resets = 0;
  total_sum_tries = 0;
  total_after_init_num_bad = 0;
  boost_on = 0;
}


void
main_init_try()
{

    if (flag_graphics) graphics_start_try();

    total_sum_tries++;

    if ((reset_weight_tries == 1 && try_this_assign == 1) ||
	(reset_weight_tries > 1 && (try_this_assign - 1) % reset_weight_tries == 0) ||
	(reset_weight_tries == -1 && current_try == 1) ||
	(reset_weight_tries < -1 && (current_try - 1) % -reset_weight_tries == 0) || 1){
	reset_weights();//将wff数组中每条子句开头的wff_str的next置1
	if (flag_trace) printf("Resetting weights\n");
    }

    init_assign_values();//随机初始化了assign[].value & first_init_value & value_low & pre_low值都一样
    init_diff();//初始化了assign[].diff & make
    init_tabu();//使tabu_in=0和tabu_out=0
    init_buckets();//初始化了assign.maxdiff[pos,list]和walk[pos,list].具体解说进函数看注释并参考画图

    if (flag_anneal) anneal_initialize();

    /* initialize the directional counts */
    downwards_count = 0;
    sideways_count = 0;
    upwards_count = 0;
    null_count = 0;

    current_num_bad = get_bad_clauses(0, 0); /* Initialize global variable *///用逐个扫描的方法判断当前的unsat子句数
    init_bad = current_num_bad;
    
    /* printf("Initial current_num_bad=%d\n", current_num_bad); */
    /* print_assign_stdout(); */
    
    total_after_init_num_bad += current_num_bad;
    low_bad = BIG;

    if (flag_trace & FLAG_TRACE_ASSIGN)
      print_assign_stdout();

    if (flag_graphics) graphics_end_try_initialization();
}

void
main_gather_try_stats()
{
      total_downwards += downwards_count;
      total_upwards += upwards_count;
      total_sideways += sideways_count;
      total_sum_flips += downwards_count + upwards_count + sideways_count;

      total_null += null_count;

      update_positive_count();

      if (get_bad_clauses(flag_trace & FLAG_TRACE_CLAUSES, (reset_weight_tries != 0)) != current_num_bad) {
	  crash_and_burn("ERROR: current_num_bad is wrong!\n");
      }

      /* Note: do NOT save best if no better than previous best, soas not to make the best_flip etc
	 values appear unnecessarily large! */
      if (current_num_bad < best_num_bad)
	save_current_as_best();

      if (flag_save_best_max && current_num_bad > low_bad && low_bad > flag_save_best_max){
	  printf("\n** WARNING ** assignment corresponding to actual low_bad=%d not saved,\n", low_bad);
	  printf("               because flag_save_best_max=%d is too small.\n", flag_save_best_max);
	  printf("               Instead, final current_num_bad=%d is saved.\n\n", current_num_bad);
      }
      /* Note that test is <=, so low is updated at end of try even if no better than former low */
      /* This is important for adaptive starts. */
      if (current_num_bad <= low_bad || low_bad > flag_save_best_max){
	  save_current_as_low();
	  if (current_num_bad < low_bad) low_bad = current_num_bad;
      }

      update_bad_clause_count(low_bad);
      if (low_bad == 0 || (try_this_assign % reset_tries == 0)){
	  update_reset_bad_clause_count(low_bad);
      }

      if (current_num_bad == 0) {
	  total_num_assigns++;
	  total_sum_successful_flips += flip;
	  total_successful_flips_incl_resets += flip + 
	    ((try_this_assign - 1) % reset_tries) * max_flips;
	  total_successful_reset_count += ((try_this_assign-1)% reset_tries )+1 ;
      }
      if (current_try % report_interval == 0){
	  experiment_seconds += elapsed_seconds();
	  print_report("INTERMEDIATE REPORT");
	  elapsed_seconds();
      }

      if (flag_trace) print_try_statistics();
}


void
main_wrapup(PROTO(char *) msg)
PARAMS(char * msg; )
{

  experiment_seconds += elapsed_seconds();

  print_report(msg);
  if (flag_trace) print_best_statistics();
  print_assignment_file();

  if (best_num_bad == 0 && check_assign_best()==0) {
      crash_and_burn("ERROR!  Thought best_num_bad was 0, but assignment no good!\n");
      }
  if (best_num_bad != 0 && check_assign_best()==1) {
      crash_and_burn("ERROR!  Thought best_num_bad was >0, but assignment satisfies!\n");
  }

  if (flag_graphics) graphics_terminate();

}

long 
super(PROTO(int) i)
PARAMS(int i; )
{
    long power;
    int k;

    if (i<=0){
	fprintf(stderr, "bad argument super(%d)\n", i);
	exit(1);
    }
    /* let 2^k be the least power of 2 >= (i+1) */
    k = 1;
    power = 2;
    while (power < (i+1)){
	k += 1;
	power *= 2;
    }
    if (power == (i+1)) return (power/2);
    return (super(i - (power/2) + 1));
}

/***************/
/*  MAIN       */
/***************/

int
main(PROTO(int) argc, PROTO(char **) argv)
PARAMS( char ** argv; int argc; )
{
  int var;//变量个数？
  int base_max_flips;

  struct tms *a_tms;
  long begintime, endtime, mess;

  a_tms = (struct tms*)malloc(sizeof (struct tms));
  mess = times(a_tms);
  begintime = a_tms->tms_utime;
  // YZ
  //long begintime = clock();
  // YZ END
  main_init_experiment(argv, argc);
  base_max_flips = max_flips;//早就在不知到哪个函数里就被初始化了

  current_try = 0; try_this_assign = 0; 
  while (current_try < max_tries) {
      current_try++;  try_this_assign++;

      flip = 0;
      main_init_try();

      if (flag_superlinear) max_flips = base_max_flips * super(try_this_assign);

      while (flip < max_flips || (boost_on && flip < max_flips + boost_amount)){

	  if (flag_graphics) graphics_start_flip();

	  if (current_num_bad == 0) break;
	  current_max_diff = compute_max_diff();//实际上初始时就等于current_max_diff
	  if (flag_direction == 1 && current_max_diff <= 0) break;
	  if (flag_direction == 2 && current_max_diff < 0) break; 
	  if (flag_bigflip){
	      flip++;
	      big_flip();
	  }
	  else {//如果没有bad_clause的话在上上上上个if就被break了，所以到else的一定有bad_clause
	      var = pick_rand_var();//函数调用过去调用过来最后basic gsat还是用的random()函数,随机在有最大diff的那些字母中选了一个
	      if (var == 0) break;
	      flip++;
	      flip_var(var);//3-4
	  }
	  if (flip == max_flips && current_num_bad <= boost_threshhold){
	      boost_on = 1;
	      if (flag_trace) printf("BOOSTING\n");
	  }
      }
      main_gather_try_stats();
      if (current_num_bad == 0){
	  try_this_assign = 0;
	  if (flag_multiple_assigns != 1) {
	      break;
	  }
      }
  }
  main_wrapup(NULL);
  // YZ
  //long endtime = clock();
  //printf("time: %ld \n", endtime-begintime);
  // YZ END
  mess = times(a_tms); endtime = a_tms->tms_utime;
  fprintf(stdout, "c Done (mycputime is %5.3f seconds)\n", ((double)(endtime - begintime) / ((double)CLOCKS_PER_SEC / (double)10000)));
  return(0);
}
