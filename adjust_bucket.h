#define adjust_bucket(VARPTR) \
{ \
    /* printf("adjusting bucket for var=%d, cmd=%d, diff=%d\n", VARPTR->name, current_max_diff, VARPTR->diff); */\
    if (! is_in(tabu, VARPTR)){ /*该变量在tabu列表里，VARPTR->tabu.pos*/\
	if (flag_hillclimb){ /*未启用爬山算法，忽略*/\
	    if (VARPTR->make > 0){ \
		if (! is_in(walk, VARPTR)){ \
		    add_to(walk, VARPTR); \
		} \
	    } \
	    else { \
		if (is_in(walk, VARPTR)){\
		    delete_from(walk, VARPTR);\
		    if (flag_only_unsat){\
			delete_if_in(down, VARPTR);\
			delete_if_in(up, VARPTR);\
			delete_if_in(sideways, VARPTR);\
		    }\
		} \
	    }\
	    if (!flag_only_unsat || VARPTR->make > 0){\
		if (VARPTR->diff > 0){ \
		    if (! is_in(down, VARPTR)){ \
			delete_if_in(up, VARPTR); \
			delete_if_in(sideways, VARPTR); \
			add_to(down, VARPTR); \
		    } \
		} \
		else if (VARPTR->diff == 0){ \
		    if (! is_in(sideways, VARPTR)){ \
			delete_if_in(up, VARPTR); \
			delete_if_in(down, VARPTR); \
			add_to(sideways, VARPTR); \
		    } \
		} \
		else { \
		    if (! is_in(up, VARPTR)){ \
			delete_if_in(down, VARPTR); \
			delete_if_in(sideways, VARPTR); \
			add_to(up, VARPTR); \
		    } \
		} \
	    }\
	}/*爬山算法完*/\
	else { \
	    if (VARPTR->make > 0){ \
		if (! is_in(walk, VARPTR)){/*该变量的make>0则加入walk的list里,因为flip后致使make改变*/\
		    add_to(walk, VARPTR); /**assign[VARPTR->KEY.pos = ++(assign->KEY.list)].KEY.list = (VARPTR ->name);*/\
		} \
	    } \
	    else { /*某字母flip后该字母的make=0(也许本来就=0，也许flip后才为0)*/\
		if (is_in(walk, VARPTR)){/*该字母原来的make不为0，是某字母flip后才为0的*/\
		    delete_from(walk, VARPTR);\
		    if (flag_only_unsat){\
			delete_if_in(maxdiff, VARPTR);\
		    }\
		} \
	    }\
	    if (!flag_only_unsat || VARPTR->make > 0){\
		if (VARPTR->diff > current_max_diff){ /*如果该字母的diff变成了最大，下面更新各个maxdiff*/\
		    empty_out(maxdiff); /*将以前有最大diff的那些字母的maxdiff.pos清0，并将assign[1].maxdiff.list清0*/\
		    add_to(maxdiff, VARPTR); /*更新各个maxdiff*/\
		    current_max_diff = VARPTR->diff; \
		} \
		else {/*如果该字母的diff没有变成最大*/\
		    if (is_in(maxdiff, VARPTR)){ /*该字母在某字母flip前是在最大diff列表中*/\
			if (VARPTR->diff < current_max_diff){ /*该字母在某字母flip后，diff变小了则从maxdiff中删除它. 或者没有改变，所以不做操作，仍保持在maxdiff列表中*/\
			    delete_from(maxdiff, VARPTR); \
			} \
		    }\
		    else {/*该字母在某字母flip前不在最大diff列表中*/\
			if (VARPTR->diff == current_max_diff){ /*该字母在某字母flip后它的diff变成了现在的最大diff，则将其加入列表中*/\
			    add_to(maxdiff, VARPTR); \
			} \
		    } \
		} \
	    } \
	}\
    }\
}

