/*  rate of return of a portfolio	*/
/*  Alan L. Wendt */
/*  alan@ezlink.com */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#define nelts(array) (sizeof(array) / sizeof(array[0]))

#define UNKNOWN		-1.23456e18

#define	MAXTRANS	2000
#define	MAXACCTS	200
#define MAXSTKS		200

extern char	*alloc();
extern char	*slookup();
extern char	*ncv();
static double	est(), brent();
extern char	*daytostr();
static double	cashflow();
static int acct_index(), acct_date(), stock_alpha(), acctyear_year();

static double avg();
static double estimated_price() __attribute__((unused));
static void	annual_performance();
static void postbalance();
static double simple_return_pct();
static void stop();
static void addprice();
static void atomize();

char		daystr[10];
int		debug;
int		showflows;
int		use_brent;
long		today;

#define CURRPRICE(stk) (stocks[stk].prices ?stocks[stk].prices->price : UNKNOWN)

/*	cash flows */
struct Trans {
    double	deposit;	/* amount */
    long	date;		/* date of transaction */
    int		acct;		/* account index number */
    char	fake;		/* I'm a fake transaction */
    } trans[MAXTRANS];

/*	accounts (ie magellan ira account) */
struct Acct {
    char	*name;		/* e.g. "ira" */
    int		stkix;		/* index into stknames */
    int		firsttrans;	/* 1st trans in deposits */
    long	enddate;	/* last balance date */
    double	shares;		/* current share balance */
    double	balance;	/* current dollar balance */
    } accts[MAXACCTS];


/*	stocks (ie magellan), also holds Index averages (e.g. SP500) */
struct Stock {
    char	*name;		/* e.g. "mag" */
    struct Price *prices;	/* list of all prices encountered */
    int		listed;		/* listed as an account */
    } stocks[MAXSTKS];

struct Price {			/* historical prices */
    long	date;		/* in reverse order */
    float	price;
    struct Price *prev;
    };

/*  This records the dollar balance of each acct at the end of the
 *  year, or as close to it as the data goes.  It's used to print
 *  the annual performance summary.
 *  There's one of these for each account and each year.
 */
struct AcctYear {
    short	year;		/* 1994 */
    short	day;		/* 1 to 366 */
    double	balance;
    short	acct;
    } acctyear[MAXACCTS*10];

int		nacctyears;	/* # of AcctYear structures used */

struct Year {
    int		year;		/* e.g. 1999 */
    int		firsttrans;	/* 1st trans in deposits */
    long	enddate;	/* last balance date */
    double	balance;	/* current dollar balance */
    double	deposits;	/* total deposits for this year */
    double	withdrawals;    /* total withdrawals for this year (as a negative) */
    } years[100];

int		nyears;		/* # of Year structures used */

char		*filenames[50];
int		nfiles, naccts, nstks, ntrans;
long		maxday = 0;	/* largest date encountered */
long		minday = 2000000000;	/* smallest date encountered */
char		*stock;
int		trace_est;

/*  indexes into accts to sort it alphabetically */
short		sorted_accts[MAXACCTS];

/* strtoday string into day number */


static unsigned maxd[] = {
    0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31,
    };

int getstk(stock)
    char	*stock;
    {
    int		stkno;
    stock = slookup(stock, 1);
    if (nstks > MAXSTKS) stop("too many stocks\n");

    stocks[nstks].name = stock;
    for (stkno = 0; stocks[stkno].name != stock; stkno++)
	;
    if (stkno == nstks) {
	stocks[stkno].prices = NULL;
	nstks++;
	}
    return stkno;
    }

/*  Look up an account number by stock name (e.g. magellan) and
 *  account name (e.g. ira) to find the slot that hold information
 *  about, for example, magellan stock trades in your ira account.
 */
int getacct(stock,acct)
    char	*stock, *acct;
    {
    int		stkno, acctno;

    stock = slookup(stock, 1);
    acct = slookup(acct, 1);

    stkno = getstk(stock);

    if (naccts == MAXACCTS) stop("too many accts\n");
    accts[naccts].name = acct;
    accts[naccts].stkix = stkno;

    for (acctno = 0; accts[acctno].name != acct || accts[acctno].stkix != stkno;
	acctno++)
	;

    if (acctno == naccts) naccts++;
    return acctno;
    }

/*  Here's a newer price for this stock.  Link it at the head of the chain */
static void addprice(date, stk, price)
    long	date;
    int		stk;
    float	price;
    {
    struct Price *newprice;
    newprice = (struct Price *)alloc(sizeof(struct Price));
    newprice->prev = stocks[stk].prices;
    stocks[stk].prices = newprice;
    newprice->date = date;
    newprice->price = price;
    }

static void stop(msg)
    char *msg;
    {
    fprintf(stderr, "%s\n", msg);
    exit(1);
    }

static double dexp(d, exp)
    double d;
    register long exp;
    {
    static double result;


    result = 1.0;	    /* init multiplicative acc */

    if (exp < 0)	    /* exponent negative? */
	{
	d = 1/d;
	exp = -exp;
	}

    while (exp != 0) {
	if (exp & 1) result *= d;   /* fold this factor */
	exp >>= 1;	    /* shift exponent */
	d *= d;     /* square running multiplier */
	}

    return result;
    }

#define YEAR (n[0])
#define MONTH (n[1])
#define DAY (n[2])

/*  convert "YYMMDD" into # of days using Jan 1, 1601 = day 1
 *  ref: CACM 11, 657 (1968) - valid back to 24 Nov -4713
 */
long strtoday(dd)
    char *dd;
    {
    char		*ddend;
    int			c;
    long		jdn;
    int			n[3];
    static int		m;

    jdn = strtol(dd, &ddend, 10);	/* convert yyyymmdd */

    if (*ddend) return -1;

    for (c = 2; c >= 1; c--) {		/* get dd and mm */
	n[c] = jdn % 100;
	jdn /= 100;
	}

    YEAR = jdn;

    if (YEAR <= 99) YEAR += 1900;	/* correct for c */
    maxd[2] = 28;
    if ((!(YEAR & 3) && (YEAR % 100)) || !(YEAR % 400)) 
	maxd[2] = 29;
    if (MONTH < 1 || MONTH > 12 || DAY < 1 || DAY > (int)maxd[MONTH]) return -1;

    m = (MONTH <= 2) ? -1 : 0;
    YEAR += m;
    jdn = (long)DAY - 2337888L;
    jdn += 1461L * ((long)YEAR + 4800L) / 4L;
    jdn += 367L * (MONTH - 2L - (long)m * 12L) / 12L;
    jdn -= 3L * (((long)YEAR + 4900L) / 100L) / 4L;

    return jdn;
    }

#define LO 0
#define MID 1
#define HI 2

extern double atof();

static void atomize(s, atoms)
    char	*s, **atoms;
    {
    int		i;
    char	*t;

    for (i = 0;;) {
	atoms[i++] = s;
	t = strchr(s, '\t');
	if (t) {
	    *t = 0;
	    s = t + 1;
	    }
	else {
	    atoms[i] = 0;
	    return;
	    }
	}
    }

#if 0
earns	djia	133.05		/* earnings */
divs	djia	70.06		/* dividends */
p/e	djia	15.1		/* price to earnings ratio */
p/b	djia	2.0427		/* price to book ratio */
#endif

char	*names[] = {
	"price", "date", "bal", "buy", "sell", "yield", "div",
	"what", "charge", "note", "stcg", "ltcg", "earns", "divs",
	"p/e", "p/b", "div2"
	};

static enum linetype { PRICE,DATETY,BAL,BUY,SELL,YIELD,DIV,WHAT,CHARGE,NOTE,STCG,LTCG, EARNINGS, DIVIDENDS, PTER, PTBR, COMMENT, DIV2 } type;
static enum linetype decode(name)
    char	*name;
    {
    int		i;
    if (name[0] == '#')
	return COMMENT;

    for (i = 0; i < (int)nelts(names); i++) {
	if (!strcmp(names[i], name)) {
	    return (enum linetype)i;
            }
	}
    return WHAT;
    }

static     double	totbal;

int main(ac, av)
    int		ac;
    char	*av[];
    {
    FILE	*f;
    char	bf[200], *fields[20];
    int		i, j, lineno = 0, acct, stk;
    long	period_end = 1000000000;
    double	soldshares;

    if (ac == 2 && !strcmp(av[1], "--help")) {
        printf("-d  debug\n");
        printf("-f  show cash flows\n");
        printf("-e  trace roi estimation\n");
        printf("-b  use brent estimation\n");
        printf("-t mm/dd/yy results for period ending\n");
        exit(0);
        }

    /*
    trans = (struct Trans *)calloc(sizeof(struct Trans), MAXTRANS);
    */

    for (i = 1; i < ac; i++) {
	if (av[i][0] == '-' && av[i][1] == 's') stock = av[i]+2;
	else if (!strcmp(av[i], "-d")) debug = 1;
	else if (!strcmp(av[i], "-f")) showflows = 1;
	else if (!strcmp(av[i], "-e")) trace_est = 1;
	else if (!strcmp(av[i], "-b")) use_brent = 1;
	else if (av[i][0] == '-' && av[i][1] == 't') {
	    period_end = strtoday(av[i] + 2);
	    printf("period-end = %ld\n", period_end);
	    }
	else filenames[nfiles++] = av[i];
	}

    if (nfiles == 0) {
	filenames[nfiles++] = "-";
	}

    for (i = 0; i < nfiles; i++) {	/* read in all the info		*/

	if (!strcmp(filenames[i], "-")) f = stdin;
	else f = fopen(filenames[i], "r");
	if (f == NULL) {
	    fprintf(stderr, "can't open %s\n", filenames[i]);
	    continue;
	    }

	while (fgets(bf, sizeof(bf), f)) {
	    lineno++;
	    bf[strlen(bf)-1] = 0;	/* blast newline */
	    if (strlen(bf) == 0) continue;
	    atomize(bf, fields);

	    type = decode(fields[0]);

	    switch (type) {

                /*  div security account shares dollars */
                /*  account declared a dividend and posted it into the account */
                case DIV2:
                    stk = getstk(fields[1]); 

                    /* update accounts holding this stock */
		    for (acct = 0; acct < naccts; acct++) {
			if (accts[acct].stkix == stk &&
			    accts[acct].balance != UNKNOWN &&
			    accts[acct].shares != UNKNOWN &&
			    CURRPRICE(stk) != UNKNOWN) {

                            double      price = atof(fields[4]) / atof(fields[3]);
			    addprice(today, stk, price);
			    accts[acct].enddate = today;

			    accts[acct].shares += atof(fields[3]);
			    accts[acct].balance = accts[acct].shares * price;
			    if (debug && accts[acct].balance != 0.0)
				printf("      acct %s shares %s bal %.2f\n",
				accts[acct].name, ncv(accts[acct].shares), accts[acct].balance);
			    postbalance(acct);
			    }
			}

		/*  What happens in a dividend is that the price
		 *  goes down by the amount of the dividend, but the
		 *  total account balance stays the same.
		 */
		/* FALLTHROUGH */
		case DIV:	/* div	cbu	0.05 */
		stk = getstk(fields[1]);

		/*  update accts holding this stock */
		if (debug)
		    printf("%s div %s %.2f\n",
			daystr, fields[1], atof(fields[2]));

		for (acct = 0; acct < naccts; acct++) {
		    if (accts[acct].stkix == stk &&
			accts[acct].balance != UNKNOWN &&
			accts[acct].shares != UNKNOWN &&
			CURRPRICE(stk) != UNKNOWN) {

			double	balance = accts[acct].balance;
			addprice(today, stk, CURRPRICE(stk) - atof(fields[2]));
			accts[acct].enddate = today;

			accts[acct].shares = balance / CURRPRICE(stk);
			accts[acct].balance = balance;
			if (debug && accts[acct].balance != 0.0)
			    printf("      acct %s shares %s bal %.2f\n",
			    accts[acct].name, ncv(accts[acct].shares), accts[acct].balance);
			postbalance(acct);
			}
		    }

		break;

		case COMMENT:
		break;

		case YIELD:
		case NOTE:
		case STCG:
		case LTCG:
		case EARNINGS:
		case DIVIDENDS:
		case PTER:
		case PTBR:
		break;

		case WHAT:
		fprintf(stderr, "unknown transaction line %d\n",  lineno);
		break;

		case DATETY:
		today = strtoday(fields[1]);
		if (today == -1) {
		    fprintf(stderr, "bad date at line %d\n", lineno);
		    exit(1);
		    }
		strcpy(daystr, fields[1]);
		if (today > period_end)
		    goto done;
		if (today < minday)
		    minday = today;
		if (maxday < today)
		    maxday = today;
		else
		    fprintf(stderr, "backward date at line %d\n", lineno);
		break;
	


		case PRICE: /*  price	cbu	11.31 */

		stk = getstk(fields[1]);		/* remember price */
		addprice(today, stk, atof(fields[2]));

		/*  update accts holding this stock */
		if (debug)
		    printf("%s price %s %.2f\n", daystr, fields[1], CURRPRICE(stk));
		for (acct = 0; acct < naccts; acct++) {
		    if (accts[acct].stkix == stk) {
			if (accts[acct].shares != UNKNOWN)
			    accts[acct].balance = accts[acct].shares * CURRPRICE(stk);
			accts[acct].enddate = today;
			if (debug && accts[acct].balance != 0.0)
			    printf("      acct %s shares %s bal %.2f\n",
			    accts[acct].name, ncv(accts[acct].shares), accts[acct].balance);
			postbalance(acct);
			}
		    }

		break;


		case SELL: /* sell	cbu	std	100	1119.47 */


		acct = getacct(fields[1], fields[2]);
		stk = accts[acct].stkix;

		if (strcmp(fields[3], "?")) soldshares = atof(fields[3]);
		else if (CURRPRICE(stk) != UNKNOWN)
		    soldshares = atof(fields[4]) / CURRPRICE(stk);
		else soldshares = UNKNOWN;

		if (accts[acct].shares != UNKNOWN && soldshares != UNKNOWN) {
		    accts[acct].shares -= soldshares;
		    }
		else accts[acct].shares = UNKNOWN;

		if (strcmp(fields[3], "?")) {
		    addprice(today, stk, atof(fields[4]) / atof(fields[3]));
		    }

		if (ntrans >= MAXTRANS) {
		    fprintf(stderr, "too many transactions\n");
		    exit(1);
		    }

		trans[ntrans].deposit = -atof(fields[4]);
		trans[ntrans].fake = 0;
		if (accts[acct].shares == 0) {
		    accts[acct].balance = 0.0;
		    accts[acct].enddate = today;
		    }
		if (accts[acct].shares != UNKNOWN && CURRPRICE(stk) != UNKNOWN)			   {
		    accts[acct].balance = accts[acct].shares * CURRPRICE(stk);
		    accts[acct].enddate = today;
		    }

		if (debug) {
		    printf("%s sell %s %s price %s ",
			daystr, fields[1], fields[2], ncv(CURRPRICE(stk)));
		    printf("%s shares worth ", ncv(soldshares));
		    printf("$%s ", ncv(atof(fields[4])));
		    printf("%s remain worth ", ncv(accts[acct].shares));
		    printf("$%s\n", ncv(accts[acct].balance));
		    }
		trans[ntrans].date = today;
		trans[ntrans].acct = acct;
		ntrans++;
		postbalance(acct);
		break;

		/* This is like a charge that you pay that
		 * doesn't buy you any additional shares.
		 */
		case CHARGE: /* charge	cbu	std	10.00	*/
		acct = getacct(fields[1], fields[2]);
		if (debug)
		    printf("%s charge %s %s %.2f\n",
			daystr, fields[1], fields[2], atof(fields[3]));

		if (ntrans >= MAXTRANS) {
		    fprintf(stderr, "too many transactions\n");
		    exit(1);
		    }
		trans[ntrans].deposit = atof(fields[3]);
		trans[ntrans].date = today;
		trans[ntrans].acct = acct;
		trans[ntrans].fake = 0;
		ntrans++;
		postbalance(acct);
		break;

		case BUY: /* buy	cbu	std	100	1119.47	*/

		acct = getacct(fields[1], fields[2]);
		stk = accts[acct].stkix;

		if (accts[acct].shares != UNKNOWN) {
		    if (strcmp(fields[3], "?"))
			accts[acct].shares += atof(fields[3]);
		    else if (CURRPRICE(stk) != UNKNOWN)
			accts[acct].shares += atof(fields[4]) / CURRPRICE(stk);
		    else
			accts[acct].shares = UNKNOWN;
		    }

		if (strcmp(fields[3], "?"))
		    addprice(today, stk, atof(fields[4]) / atof(fields[3]));

		if (ntrans >= MAXTRANS) {
		    fprintf(stderr, "too many transactions\n");
		    exit(1);
		    }
		trans[ntrans].fake = 0;
		trans[ntrans].deposit = atof(fields[4]);

		if (accts[acct].shares == 0) {
		    accts[acct].balance = 0.0;
		    accts[acct].enddate = today;
		    }
		if (accts[acct].shares != UNKNOWN && CURRPRICE(stk) != UNKNOWN)
		    {
		    accts[acct].balance = accts[acct].shares * CURRPRICE(stk);
		    accts[acct].enddate = today;
                    }

		if (debug)
		    printf("%s buy  %s %s price %.2f shares %s bal %.2f\n",
			daystr, fields[1], fields[2], CURRPRICE(stk),
			ncv(accts[acct].shares), accts[acct].balance);
		trans[ntrans].date = today;
		trans[ntrans].acct = acct;
		ntrans++;
		postbalance(acct);
		break;

		case BAL: /* bal	bac	std	100	862.50	*/

		acct = getacct(fields[1], fields[2]);
		stk = accts[acct].stkix;

		if (strcmp(fields[3], "?")) accts[acct].shares = atof(fields[3]);
		else if (CURRPRICE(stk) != UNKNOWN && fields[4]) {
		    accts[acct].shares = atof(fields[4]) / CURRPRICE(stk);
		    }
		else accts[acct].shares = UNKNOWN;

		if (accts[acct].shares != UNKNOWN && accts[acct].shares != 0.0) {
		    addprice(today, stk, atof(fields[4]) / accts[acct].shares);
		    }

		if (fields[4])
		    accts[acct].balance = atof(fields[4]);
		else
		    accts[acct].balance = accts[acct].shares * CURRPRICE(stk);

		if (debug)
		    printf("%s bal %s %s price %.2f shares %s bal %.2f\n",
			    daystr, fields[1], fields[2], CURRPRICE(stk),
			    ncv(accts[acct].shares), accts[acct].balance);
		accts[acct].enddate = today;
		postbalance(acct);
		break;
		}
	    }
	done:
	fclose(f);
	}

    accts[nfiles].firsttrans = ntrans;		/* remember last element */

    /*  Fake up a withdrawl on the last balance date of each account so that
     *  the cash flow will look like we got all of our money out.
     */
    totbal = 0;
    for (acct = 0; acct < naccts; acct++) {	/* for each account	*/
	if (accts[acct].balance) {
	    if (ntrans >= MAXTRANS) {
		fprintf(stderr, "too many transactions\n");
		exit(1);
		}

	    /*	The following line dumps core under Xenix 2.3.4 286 */
	    trans[ntrans].deposit = -accts[acct].balance;
	    trans[ntrans].date = accts[acct].enddate;
	    trans[ntrans].acct = acct;
	    trans[ntrans].fake = 1;
	    totbal += accts[acct].balance;
	    ntrans++;
	    }
	}

    /*  Sort the cash flow records into account order */
    qsort(trans, ntrans, sizeof(trans[0]), acct_index);

    /*  Record the first transaction index in each account */
    accts[trans[ntrans - 1].acct + 1].firsttrans = ntrans;
    for (i = ntrans - 1; i >= 0; i--)
	accts[trans[i].acct].firsttrans = i;

    printf("   stock     acct     roi       price     shares      balance  39-week\n");


    for (acct = 0; acct < naccts; acct++)
	sorted_accts[acct] = acct;
    
    /*  get a list of accounts sorted alphabetically */
    qsort(sorted_accts, naccts, sizeof(sorted_accts[0]), stock_alpha);

    for (j = 0; j < naccts; j++) {
	acct = sorted_accts[j];
	stk = accts[acct].stkix;
	stocks[stk].listed = 1;

	/*
	printf("For acct %d first %d last %d\n",
		acct,
		accts[acct].firsttrans,
		accts[acct + 1].firsttrans - 1);
	*/

	if (showflows) {
	    printf("Cash flows for %s %s:\n",
		stocks[stk].name, accts[acct].name);

	    for (i = accts[acct].firsttrans;
		i < accts[acct + 1].firsttrans; i++) {
		printf("%s\t% 9.4f\n",
		    daytostr((double)trans[i].date), trans[i].deposit);
		}
	    }

	printf("%8.8s ", stocks[stk].name);
	printf("%8.8s: ", accts[acct].name);
	printf("% 9.4f", use_brent ?
          brent(accts[acct].firsttrans, accts[acct + 1].firsttrans) :
          est(accts[acct].firsttrans, accts[acct + 1].firsttrans));
        if (stocks[stk].prices) {
            printf("%9.2f  ", stocks[stk].prices->price);
        } else {
            printf("        ?  ");
        }
	if (accts[acct].shares)
	    printf("%9.2f  ", (double)accts[acct].shares);
	else
	    printf("           ");
	if (accts[acct].balance)
	    printf("% 11.2f", (double)accts[acct].balance);
	else
	    printf("           ");
	printf("%9.2f", avg(stocks[stk].prices, 39 * 7));
	if (accts[acct].balance) {
	    printf("  %4.0f%%", accts[acct].balance / totbal * 100.0);
	    }
	printf("\n");
	}

    /*	Now list prices and 39-week averages for stocks that we have
     *  records for that we did not report as part of an account.
     */
    for (stk = 0; stk < nstks; stk++) {
	if (!stocks[stk].listed) {
	    printf("%8.8s         :          ", stocks[stk].name);
	    printf("%9.2f                        %9.2f",
		stocks[stk].prices->price, avg(stocks[stk].prices, 39 * 7));
	    printf("\n");
	    }
	}

    if (naccts)
	printf("            total: % 9.4f                      %11.2f\n",
	    use_brent ? brent(0, ntrans) : est(0, ntrans), totbal);

    /*  Delete the fake transactions */
    for (i = 0; i < ntrans; i++) {
	if (trans[i].fake)
	    trans[i--] = trans[--ntrans];
	}

    annual_performance();

    exit(0);
    }

/*  for each year in this file
 *      add up end of year balances for each account
 *  show:  balances at end of year
 *         investment returns in dollars
 *         new investing in dollars
 *         rate of investment return for the year.
 */
static void annual_performance()
    {
    int		i;
    double	previous = 0;		/* previous end-of-year balance */
    int		acct, j;
    double	totdeposits = 0, totwithdrawals = 0, totreturns = 0;
    int		yix;
    int		lastdix, firstdix;

    /*  index # of next chronological cash flow record */
    int		nexttrans;

    printf("\n\nYear   Deposits    Withdrawals       Net       Investment       Balance          Gain    Simple Roi        Roi\n");
    printf("                                                 Return\n\n");

    /*  sort the end-of-year account balances into date order */
    qsort(acctyear, nacctyears, sizeof(acctyear[0]), acctyear_year);

    /*  Sort the cash flow records (including the fakes) into date order */
    qsort(trans, ntrans, sizeof(trans[0]), acct_date);

    /*  Summarize the end-of-year account balances into the end-of-year
     *  total balance records.
     */

    /*  For each end-of-year account balance */
    for (i = 0, nexttrans = 0; i < nacctyears; i++) {

	/*  Is i the last year-end-balance record for some year? */
	if (i == nacctyears - 1 || acctyear[i].year != acctyear[i + 1].year) {

            /*  end of this year */
            years[nyears].year = acctyear[i].year;

	    /*  Add up the deposits made in acctyear[i].year */
	    for (; nexttrans < ntrans; nexttrans++) {
		char	bf[20];
		int		year;
		char	*s;
		strcpy(bf, daytostr((double)trans[nexttrans].date));
		s = strrchr(bf, '/');
		year = strtol(s + 1, (char **)NULL, 10);
		if (year != acctyear[i].year)
		    break;
                if (trans[nexttrans].deposit < 0) {
		    years[nyears].withdrawals += trans[nexttrans].deposit;
                } else {
                    years[nyears].deposits += trans[nexttrans].deposit;
		}
            }

	    /*  Add up the most recent balance for each acct prior to
	     *  the end of that year.
	     */
	    years[nyears].balance = 0;

	    for (acct = 0; acct < naccts; acct++) {
		/*  Find most recent acctyear record for this acct */
		for (j = i; j >= 0; j--) {
		    if (acctyear[j].acct == acct) {
                        char bf[512];
			years[nyears].balance += acctyear[j].balance;
                        sprintf(bf, "%d1231", years[nyears].year);
                        years[nyears].enddate = strtoday(bf);
			break;
			}
		    }
		}

	    /*  Fake up a withdrawl on the last balance date of each
             *  year so that the cash flow will look like we got
             *  all of our money out.
	     */
	    /* if (years[nyears].balance) { */
		if (ntrans >= MAXTRANS) {
		    fprintf(stderr, "too many transactions\n");
		    exit(1);
		    }

		trans[ntrans].deposit = -years[nyears].balance;
		trans[ntrans].date = years[nyears].enddate;
		trans[ntrans].fake = 1;
		ntrans++;
		/* } */

#if 0
	    printf("year %d date %d %s %s deposits %.2f bal %.2f\n",
		acctyear[i].year,
		acctyear[i].day,
		accts[acctyear[i].acct].name,
		stocks[accts[acctyear[i].acct].stkix].name,
		years[i].deposits, acctyear[i].balance);
#endif
	    totdeposits += years[nyears].deposits;
            totwithdrawals += years[nyears].withdrawals;
	    totreturns += years[nyears].balance - previous - (years[nyears].deposits + years[nyears].withdrawals);
	    previous = years[nyears].balance;
            nyears++;
	    }
	}

    /*  All the fakes got December 31 dates, but this is
     *  wrong for the partial last year.
     */
    trans[ntrans - 1].date = today;

    /*  Sort the cash flow records (including the fakes) into date order */
    qsort(trans, ntrans, sizeof(trans[0]), acct_date);

    /*  Set the years[i].firsttrans values */
    years[nyears].firsttrans = ntrans;
    yix = nyears - 1;
    for (i = ntrans - 1; 0 <= i; i--) {
        char bf[512], *s;
        int year;
	strcpy(bf, daytostr((double)trans[i].date));
	s = strrchr(bf, '/');
	year = strtol(s + 1, (char **)NULL, 10);
        while (year < years[yix].year && 0 <= yix)
            yix--;
        years[yix].firsttrans = i;
        }

    previous = 0.0;

    /*  Handle first year separately. */
    lastdix = years[1].firsttrans - 1;
    trans[lastdix].deposit = -years[0].balance;

    /* printf("\n\nYear   Deposits    Withdrawals   Net       Investment       Balance          Gain          Roi\n"); */
    printf("%4d %10.2f    %10.2f    %10.2f    %10.2f    %10.2f                %10.2f%% %10.2f%%\n",
	years[0].year, years[0].deposits, years[0].withdrawals, years[0].deposits + years[0].withdrawals,
	years[0].balance - (years[0].deposits + years[0].withdrawals),
	years[0].balance,
        simple_return_pct(
            years[0].balance - (years[0].deposits + years[0].withdrawals),
            years[0].deposits + years[0].withdrawals
        ),
        est(0, lastdix + 1));

    /*  Print info for each subsequent year */
    for (i = 1; i < nyears; i++) {

	/*  Fake up a deposit on last day of prior year */  
	firstdix = years[i].firsttrans - 1;
	if (0 <= firstdix) {
	    trans[firstdix].deposit = years[i - 1].balance;
	    }

	/*  Update the fake to look like a withdrawl on last day of this year */
	lastdix = years[i + 1].firsttrans - 1;
	trans[lastdix].deposit = -years[i].balance;

	printf("%4d %10.2f    %10.2f    %10.2f    %10.2f    %10.2f    %10.2f%% %10.2f%% %10.2f%%\n",
            /* year */
	    years[i].year,
            /* deposits */
            years[i].deposits,
            years[i].withdrawals,
	    years[i].deposits + years[i].withdrawals,
            /* investment return */
	    years[i].balance - years[i - 1].balance - (years[i].deposits + years[i].withdrawals),
            /* balance */
	    years[i].balance,
            /* Percent growth over previous year */
	    years[i].balance / years[i - 1].balance * 100.0 - 100.0,
            /* simple period roi */
            simple_return_pct(
                years[i].balance - years[i - 1].balance - (years[i].deposits + years[i].withdrawals),
                years[i - 1].balance + years[i].deposits + years[i].withdrawals
            ),
            /* roi */
	    est(firstdix, lastdix + 1)
            );
	}

    printf("     %10.2f    %10.2f    %10.2f    %10.2f\n", totdeposits, totwithdrawals, totdeposits + totwithdrawals, totreturns);
    }

static double simple_return_pct(gain, base)
    double gain;
    double base;
    {
    if (base == 0.0)
        return 0.0;
    return gain / base * 100.0;
    }

#if 0
/* Add up all the cash flows for this "account", plus interest
 * at the given rate.  Assumes that transactions are sorted
 * into account order.
 *
 * If acct == -1, adds up all the cash flows.
 * Else if acct < 0, add up all cash flows for the year index 2 - acct.
 * Else add up all cash flows for the given account index.
 */
static double acct_cashflow(int acct, double rate)
    {
    int		lb, ub, i;
    double	result;

    if (acct == -1) {				/* everything */
	lb = 0;
	ub = ntrans;
	}
    else if (acct < 0) {			/* one year's worth */
        acct = -2 - acct;			/* get year index */
        lb = years[acct].firsttrans - 1;	/* pick up fake deposit */
        if (lb < 0)				/* first year? */
           lb = 0;				/* yes, no fake deposit */
        ub = years[acct + 1].firsttrans;
        }
    else {					/* one account's worth */
	lb = accts[acct].firsttrans;
	ub = accts[acct + 1].firsttrans;
	}

    return cashflow(rate, lb, ub, maxday);
    }
#endif

/*  Add up all of the cash flows, plus interest at the given rate */
double cashflow(rate, lb, ub, endperiod)
    double	rate;		/* interest rate */
    int		lb;		/* first transaction index */
    int		ub;		/* last transaction index + 1 */
    long	endperiod;	/* end of period date */
    {
    int		i;
    double	result;

    /*  Calculate the total cashflow for this rate */
    result = 0;
    for (i = lb; i < ub; i++) {
	if (trans[i].date == 0)
	    return 0;
	result += (trans[i].deposit * dexp(rate, endperiod - trans[i].date));
	}
    return result;
    }

/*  Estimate rate of return on investment by binary and linear search */
static double est(int lb, int ub)
    {
    int		which;
    double	guess[3], tot[3];
    int		i;


    /*  get initial upper bound by doubling the estimate	*/
    /*  We have to start off with good bounds because we may	*/
    /*  be raising them to very large exponents.		*/
    guess[HI] = 1.0000001;	/* lower bound on the upper bound	*/
    do	{
	guess[HI] = 1.0 + 2.0 * (guess[HI] - 1.0);
	tot[HI] = cashflow(guess[HI], lb, ub, maxday);
	} while (tot[HI] < 0.0);

    /*  get initial lower bound			*/
    guess[LO] = guess[HI];
    i = 0;
    do	{
	guess[LO] *= 0.99;
	tot[LO] = cashflow(guess[LO], lb, ub, maxday);
        if (++i > 1000)
          return NAN;
	} while (0 < tot[LO]);

    if (tot[LO] == tot[HI])
	return 0.0;

    /*  Uses alternating linear (secant) and bisection search steps because
     *  secant sometimes blows up on negative interest rates.  I have never
     *  seen more than 12 pairs of steps needed to drive the accuracy to
     *  machine precision.  The loop breaks when the machine's arithmetic does.
     */
    for (;;) {


	/* Guess the rate that will yield zero total cashflow (secant) */
	guess[MID] = guess[LO] + (guess[HI] - guess[LO]) *
			-tot[LO] / (tot[HI] - tot[LO]);

	if (trace_est)
	    printf("LINEAR: LOW %.8g MID %.8g HI %.8g INT %.8g\n",
		(double)guess[LO], (double)guess[MID],
		(double)guess[HI], (double)guess[HI] - (double)guess[LO]);

	tot[MID] = cashflow(guess[MID], lb, ub, maxday);

	which = (0 < tot[MID]) ? HI : LO;

	if (guess[LO] >= guess[HI] /* || guess[which] == guess[MID] */)
	    goto gotrate;

	guess[which] = guess[MID];
	tot[which] = tot[MID];

	/* special step */
	if (which == LO)
	    guess[MID] = guess[LO] + (guess[HI] - guess[LO]) / 10.0;
	else
	    guess[MID] = guess[HI] - (guess[HI] - guess[LO]) / 10.0;

	if (trace_est)
	    printf("SPCIAL: LOW %.8g MID %.8g HI %.8g INT %.8g\n",
		(double)guess[LO], (double)guess[MID],
		(double)guess[HI], (double)guess[HI] - (double)guess[LO]);

	/*  Calculate the total cashflow for this rate */
	tot[MID] = cashflow(guess[MID], lb, ub, maxday);

	which = (0 < tot[MID]) ? HI : LO;

	if (guess[LO] >= guess[HI] /* || guess[which] == guess[MID] */)
	    goto gotrate;

	guess[which] = guess[MID];
	tot[which] = tot[MID];

	/* Bisection step */
	guess[MID] = (guess[HI] + guess[LO]) / 2;

	if (trace_est)
	    printf("BISECT: LOW %.8g MID %.8g HI %.8g INT %.8g\n",
		(double)guess[LO], (double)guess[MID],
		(double)guess[HI], (double)guess[HI] - (double)guess[LO]);

	tot[MID] = cashflow(guess[MID], lb, ub, maxday);

	which = (0 < tot[MID]) ? HI : LO;

	if (guess[LO] >= guess[HI] || guess[which] == guess[MID]) break;

	guess[which] = guess[MID];
	tot[which] = tot[MID];
	}

    gotrate:
    guess[MID] = 100.0 * (dexp(guess[MID], (long)365) - 1.0);
    return guess[MID];
    }

char *ncv(d)
    double d;
    {
    static char bf[50];
    if (d == UNKNOWN) return "?";
    sprintf(bf, "%.2f", d);
    return bf;
    }

#define DAYBUFL 11

/* Convert day number to string */
char *daytostr(djd)
    double djd;
    {
    long	jd, l, n, y, m, d;
    static char buffer[DAYBUFL];		/* date conversion buffer */

    if (djd == UNKNOWN) return "?";
    jd = djd;				/* integer version */

    l = jd + 2374382L;
    n = 4L*l / 146097L;
    l = l - (146097L*n + 3L)/4L;
    y = 4000L* (l+1L) / 1461001L;
    l = l-1461L * y / 4L +31L;
    m = 80L * l / 2447L;
    d = l - 2447L * m /80L;
    l = m /11L;
    m = m + 2L - 12L * l;
    y = 100L* (n-49L) + y + l;
    if (1900L <= y && y <=1999L)
	sprintf(buffer, "%2u/%02u/%02u", (unsigned)m,
	    (unsigned)d, (unsigned)(y-1900));
    else
	sprintf(buffer, "%2u/%02u/%04u", (unsigned)m,
	    (unsigned)d, (unsigned)y);
    return buffer;
    }

/*  Compare two transactions to sort them into date order.
 *  Sort fakes after non-fakes.
 */
static int acct_date(l,r)
    struct Trans *l, *r;
    {
    if (l->date < r->date) return -1;
    if (l->date > r->date) return 1;
    if (l->acct < r->acct) return -1;
    if (l->acct > r->acct) return 1;
    if (l->fake > r->fake) return 1;
    if (l->fake < r->fake) return -1;
    return 0;
    }

static int acctyear_year(l, r)
    struct AcctYear *l, *r;
    {
    if (l->year < r->year)
	return -1;
    if (l->year > r->year)
	return 1;
    return 0;
    }

/*  Compare two transactions to sort them into account order and bring
 *  transactions for the same accounts into a tight sequence.
 */
static int acct_index(l,r)
    struct Trans *l, *r;
    {
    if (l->acct < r->acct) return -1;
    if (l->acct > r->acct) return 1;
    if (l->date < r->date) return -1;
    if (l->date > r->date) return 1;
    return 0;
    }

/*  Compare accounts to generate a list of accounts sorted alphabetically */
static int stock_alpha(l,r)
    short	*l, *r;
    {
    int		cmp;

    cmp = strcmp(stocks[accts[*l].stkix].name,
		 stocks[accts[*r].stkix].name);
    if (cmp < 0)
	return -1;
    if (cmp > 0)
	return 1;

    cmp = strcmp(accts[*l].name, accts[*r].name);

    if (cmp < 0)
	return -1;
    if (cmp > 0)
	return 1;

    return 0;
    }

#define EPS 3.0e-16

/*  From Numeric Algorithms in C */
static double brent(int lb, int ub)
    {
    int		iter;
    double	a, b;		/* upper and lower bounds */
    double	c = 0.0, d = 0.0, e = 0.0, min1, min2;
    double	fa, fb, fc, p, q, r, s, tol1, xm;

    /*  get initial upper bound by doubling the estimate	*/
    /*  We have to start off with good bounds because we may	*/
    /*  be raising them to very large exponents.		*/
    a = 1.0000001;	/* lower bound on the upper bound	*/
    do	{
	a = 1.0 + 2.0 * (a - 1.0);
	fa = cashflow(a, lb, ub, maxday);
	} while (fa <= 0.0);

    /*  get initial lower bound			*/
    b = a;
    do	{
	b *= 0.99;
	fb = cashflow(b, lb, ub, maxday);
	} while (0 <= fb);

    if (fb * fa > 0.0) {
	fprintf(stderr, "Root must be bracketed in ZBRENT\n");
	exit(-1);
	}
    
    fc = fb;

    /*  f(a) & f(b) bracket the root and c is between a & b */

    for (iter = 1; iter < 100; iter++) {

	if (fb * fc > 0.0) {		/* b & c on same side */
	    c = a;			/* use a & b */
	    fc = fa;			/* now b & c are limits */
	    e = d = b - a;
	    }

	if (fabs(fc) < fabs(fb)) {	/* if c is closer to root */
	    a = b;			/* use */
	    b = c;
	    c = a;
	    fa = fb;
	    fb = fc;
	    fc = fa;
	    }

	tol1 = 2.0 * EPS * fabs(b);
	xm = 0.5 * (c - b);

	if (fabs(xm) <= tol1 || fb == 0.0) {
	    /* fprintf(stderr, "xm %.8g tol1 %.8g fb %.8g\n", xm, tol1, fb); */
	    return 100.0 * (dexp(b, (long)365) - 1.0);
	    }

	if (fabs(e) >= tol1 && fabs(fa) > fabs(fb)) {
	    s = fb / fa;
	    if (a == c) {
		p = 2.0 * xm * s;
		q = 1.0 - s;
		}
	    else {
		q = fa / fc;
		r = fb / fc;
		p = s * (2.0 * xm * q * (q - r) - (b - a) * (r - 1.0));
		q = (q - 1.0) * (r - 1.0) * (s - 1.0);
		}
	    if (p > 0.0)
		q = -q;
	    p = fabs(p);
	    min1 = 3.0 * xm * q - fabs(tol1 * q);
	    min2 = fabs(e * q);
	    if (2.0 * p < (min1 < min2 ? min1 : min2)) {
		e = d;
		d = p / q;
		if (trace_est)
		    printf("INTERP: b=%.8g e=%.8g\n", b, e);
		}
	    else {
		d = xm;
		e = d;
		if (trace_est)
		    printf("BISECT: b=%.8g e=%.8g\n", b, e);
		}
	    }
	else {
	    d = xm;
	    e = d;
	    if (trace_est)
		printf("BISECT: b=%.8g e=%.8g\n", b, e);
	    }

	a = b;
	fa = fb;
	if (fabs(d) > tol1)
	    b += d;
	else
	    b += (xm > 0.0) ? fabs(tol1) : -fabs(tol1);
	fb = cashflow(b, lb, ub, maxday);
	if (trace_est)
	    printf("fb=%.10g\n", fb);
	}

    fprintf(stderr, "Maximum number of iterations exceeded in ZBRENT\n");
    exit(-1);
    }

/*  Estimate the price of this stock on this given date. */
static double estimated_price(latestprice, date)
    struct Price *latestprice;
    long	date;
    {
    struct Price *current;	/* current Price record */
    struct Price *prev;		/* previous (next on list, prior datewise) */

    for (current = latestprice;; current = prev) {
	prev = current->prev;

	/*  found exactly the date we want? */
	if (current->date == date)
	    return current->price;

	/*  is prev <= date < current? */
	if (prev && prev->date <= date && date < current->date) {
	    /*  return prev price + change per day * # of days */
	    return prev->price +
		(current->price - prev->price) / (current->date - prev->date) *
		(date - prev->date);
	    }

	/*  no more dates before this one? */
	if (!prev) {
	    return current->price;
	    }
	}
    }


/*  N-day moving average.  Interpolates around missing weekday prices.
 *  Saturdays and Sundays are ignored except for the purpose of counting
 *  days -- a 39-week moving average is 39*7 days.
 *
 *  There are a few problematic cases.  If the earliest listed price
 *  might not be early enough, in which case we will have to settle for
 *  less than 39 weeks, won't we?  It might be too early, in which case
 *  the routine interpolates to get the date and price to begin the
 *  39-week period with.
 */
#define trace_avg 0
static double avg(latestprice, days)
    struct Price *latestprice;
    int		days;
    {
    struct Price *current;	/* current Price record */

    struct Price *prev;		/* next earlier record */
    long	prevdate;	/* date in prev record */

    long	date0;		/* date immediately before period */
    double	price0;		/* corresponding price */

    int		weekdays;
    double	totaldays = 0, totalprices = 0;
    long	d;
    double	delta;		/* per-day delta */

#if trace_avg
    printf("avg from %ld to %ld inclusive\n",
	latestprice->date - days + 1, latestprice->date);
#endif

    if (latestprice == 0)
        return 0.0;

    /*  Get the previous n-day avg price of this stock.  Ignores dividends. */
    for (current = latestprice;; current = prev) {

	/*  The previous date for which we have a price */
	prev = current->prev;

	/*  If there is no previous date, use current date - 1 */
	prevdate = (prev == NULL) ? current->date - 1 : prev->date;

#if trace_avg
	if (prev)
	    printf("previous date %ld price %.2f\n",
		(long)prev->date, prev->price);
	else printf("end of list, using prevdate=%ld\n", prevdate);
#endif

	/*  if the previous date was before the period started, get the
	 *  first date in the period.
	 */
	date0 = prevdate;
	if (date0 < latestprice->date - days) {
	    date0 = latestprice->date - days;
#if trace_avg
	    printf("preceeds beginning of period, using %ld\n", date0);
#endif
	    if (prev) {
		delta = (double)(current->price - prev->price) /
					(current->date - prev->date);
		price0 = prev->price + (date0 - prev->date) * delta;
#if trace_avg
		printf(
		"previous rec [%ld,%.4f] delta %.4f virtual [%ld,%.4f]\n",
		    prevdate, prev->price,
		    delta,
		    date0, price0);
#endif
		}
	    else {
		delta = price0 = 0;
#if trace_avg
		printf("No previous record\n");
#endif
		}
	    }

	/*  Get # of weekdays in the interval (date0, current] */
	weekdays = 0;
	for (d = date0 + 1; d <= current->date; d++)
	    if (1 <= d % 7 && d % 7 <= 5)
		weekdays++;

#if trace_avg
	printf("date0 %ld current->date %ld weekdays %d\n",
	    date0, current->date, weekdays);
#endif

	/*  Get sum of all of the linearly scaled prices from
	 *  date0 + 1 to date.
	 *  the two dates. date = upper date, date0 = lower date.
	 *  sum from i=1 to date - date0
	 *  (Price(date0) + i * (Price(date) - Price(date0)) /
	 *					     (date - date0))
	 *  Average of first & last = (first + last) / 2
	 *  Desired sum = (weekdays + 1) * average - first
	 */
	if (weekdays == 1)
	    totalprices += current->price;
	else if (weekdays > 0) {
	    delta = (double)(current->price - prev->price) /
				(current->date - prev->date);
	    price0 = prev->price + (date0 - prev->date) * delta;
	    totalprices +=
		(weekdays + 1.0) * (price0 + current->price) / 2.0 - price0;
	    }

	totaldays += weekdays;
	if (!prev || prev->date <= latestprice->date - days)
	    break;
	}

    return totalprices / totaldays;
    }


/*  Figure out what day it is and how much money I have.  Add the figure
 *  to the appropriate AcctYear structure, if it's closer to the end of
 *  the year than currently posted.
 */
static void postbalance(acct)
    int		acct;
    {
    char	bf[20];
    int		year, day;
    int		i;
    char	*s;

    strcpy(bf, daytostr((double)today));
    s = strrchr(bf, '/');
    year = strtol(s + 1, (char **)NULL, 10);
    sprintf(bf, "%02d0101", year);
    day = floor(1.5 + today - strtoday(bf));
    /*
    printf("string %s year %d day %d date %s\n",
	bf, year, day, daytostr((double)today));
    */
    for (i = 0; i < nacctyears; i++) {
	if (acctyear[i].year == year && acctyear[i].acct == acct) {
	    if (acctyear[i].day <= day) {
		acctyear[i].balance = accts[acct].balance;
		acctyear[i].day = day;
		}
	    return;
	    }
	}

    acctyear[nacctyears].year = year;
    acctyear[nacctyears].day = day;
    acctyear[nacctyears].acct = acct;
    acctyear[nacctyears].balance = accts[acct].balance;
    nacctyears++;
    }

#if 0
struct AcctYear {
    short	year;		/* 1994 */
    short	day;		/* 1 to 366 */
    double	balance;
    } acctyear[100];
#endif
