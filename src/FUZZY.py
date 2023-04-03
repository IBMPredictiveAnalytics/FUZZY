

#match cases in a dataset with those in a second dataset agreeing on all the key variables.

#Licensed Materials - Property of IBM
#IBM SPSS Products: Statistics General
#(c) Copyright IBM Corp. 2009, 2020
#US Government Users Restricted Rights - Use, duplication or disclosure restricted by GSA ADP Schedule Contract with IBM Corp.

# The function accepts two or three datasets.
# demanderds contains the cases for which matches are needed
# supplierds contains the cases from which matches will be drawn
# ds3 optionally is created containing the cases drawn for matching.
# These are all datasets: other code must open and save them.
# Typically supplierds will be much larger than demanderds.
# Matches are exact: they consist of agreement on n identically named variables in demanderds and supplierds
# Up to k variables are added to demanderds containing the id's for the matches.  Typically k=1.
# For unmatched cases, the id is sysmis if numeric and blank otherwise
# A hash of the match variables is included in demanderds and ds3 (domain is 32-bit integers) if requested.
# Matching can be done with or without replacement.  By default, without replacement is used.
# Specified variables can be copied from supplierds to demanderds if there is a match
# 
# Some errors are just left to raise obscure exceptions.


__author__ = "JKP, SPSS"
__version__ = "2.0.0"

# history
# 20-jan-2010  use processcmd, enable translation
# 16-feb-2010  fix letter case handling in COPYTODEMANDER keyword
#  23-jun-2010  translatable procedure name
# 01-mar-2011 distinguish exact and fuzzy counts when not using exactpriority
# 23-mar-2011 better error reporting for undefined variables
# 24-aug-2011 add rejection statistics and optional count variable
# 06-apr-2012 better handling of duplicate variable name in ds3
# 12-apr-2012 Allow supplier and demander data to be in the same input file
# 16-jul-2012 Allow custom fuzz function
# 03-jan-2013 Add logging support, redesign minimize memory approach
# 19-sep-2022 Add demander and supplier counts to output.
# 20-mar-2023 Allow for best match.  No longer support minimizememory
#             New matching algorithm

import spss, spssaux
import random, sys, locale, logging, time, bisect
from collections import namedtuple

Supp = namedtuple('Supp', ["casenum", "diff", "suppcase"])



# The following code defines the SPSS syntax and implements the Run method.  The function
# can be run as the FUZZY command using SPSS syntax or used directly as a Python function

from extension import Template, Syntax, processcmd

helptext = r"""FUZZY
Match cases from two datasets drawing randomly from matching cases.

Note: the original version of this command was called CASECTRL.  FUZZY
is a superset of that functionality.

FUZZY DEMANDERDS=dsname SUPPLIERDS=dsname BY=list of keys
SUPPLIERID=varname NEWDEMANDERIDVARS=list of variable names

Optional parameters:
GROUP = variablename
FUZZ = list-of-matching-tolerances
CUSTOMFUZZ = user-written function for calculating match eligibility
EXACTPRIORITY={TRUE*|FALSE}

COPYTODEMANDER=list of supplier variable names
MATCHGROUPVAR = variable name (default is "matchgroup")
DRAWPOOLSIZE = variable name (no default)
DEMANDERID = variable name
DS3 = dataset name
/OPTIONS
  SAMPLEWITHREPLACEMENT=TRUE or FALSE (default)
  MINIMIZEMEMORY = TRUE (default) or FALSE
  SHUFFLE = TRUE or FALSE (default)
  SEED = number
  
[/OUTFILE LOGFILE=filespec LOGACCESSMODE={OVERWRITE* | APPEND}]
/HELP.

Example:
FUZZY DEMANDERDS=demand SUPPLIERDS = supply BY=agegroup gender
SUPPLIERID = id NEWDEMANDERIDVARS=supplierId.

Example using a single input dataset (the active dataset):
FUZZY by=x1 supplierid = id newdemanderidvars=sid group=group
drawpoolsize=drawpool.
  
FUZZY takes two datasets, a demander and a supplier or a single dataset with a 
group identification variable.  It attempts to find a match for each
demander case from the supplier dataset based on the variables named in BY.  If more than one 
candidate matches, it picks randomly.  No sorting of either dataset is required.

If using a single dataset, the DEMANDERDS and SUPPLIERDS keywords
can be omitted.  The active dataset will be used.

By default, a match is defined by identical values for all the BY variables.  A system-missing
value prevents a case from being matched.  Fuzzy matching is also available for numeric variables.
Specify FUZZ=list-of-matching tolerances.  There must be one fuzz value for each BY variable,
listed in BY-value order.

A tolerance is the maximum difference in either direction that is allowed for a match.  Thus,
values of 1 and 2 would match if tolerance is 1 or more, and a tolerance of zero means an
exact match on that variable.  You must use 0 for any string variable.  If FUZZ is used,
rejection counts for each variable are show in the output.

By default, with fuzzy matching, an exact match is first tried, and then a fuzzy match is tried.
There is no attempt to get the closest fuzzy match, just a match within the tolerance.
EXACTPRIORITY = FALSE causes all suppliers within the fuzz range to be considered equally.
EXACTPRIORITY must be FALSE if MINIMIZEMEMORY is TRUE.

Using EXACTPRIORITY may introduce a subtle artifact that may need to be considered in
subsequent analysis.  While it will generally produce closer matches, cases with variable values 
where candidates are scarce will tend to get matches that differ more than where candidates
are abundant.

CUSTOMFUZZ can be used to substitute a user-written calculation for the
built-in fuzzy calculation.  It should specify a Python module name and function
as a quoted string, e.g. "mymodule.fuzzycalc".  The function should return
0 - no match
1- fuzzy match.
It coudl also return 2 (exact match).
If the case comparison produced an exact match, this function is not called.
The function signature should be
functionname(demander, supplier)
where demander and supplier are lists of the BY variable values for the
demander and supplier cases.
Note that the function needs to deal with missing values (None) and may
need to handle both string and numeric comparisons.
The FUZZ subcommand is ignored if a customfuzz function is used.

The DEMANDERDS and SUPPLIERDS values can be the same, indicating that all the data
is in the same dataset.  In this case, GROUP must be used to distinguish the cases.
GROUP names a variable that indicates which are demander cases and which supplier ones.
A value of 1 indicates demander and 0 indicates supplier.  Any other values, including missing,
cause the case to be ignored.

This procedure builds some possibly large tables in memory, so it may not be appropriate for very
large datasets.


There are several output options.
The ID or IDs of matching cases are appended to the demander dataset variables.  The number of
variables listed as NEWDEMANDERIDVARS determines how many matches are attempted.  These variables
must not already exist in the demander dataset.

The variables in the supplier dataset that are listed in COPYTODEMANDER are copied to the 
demander dataset as new variables or replacement values.  For existing variables, the types 
must agree.  If no match is found, existing demander dataset values are not changed and new
variable values will be sysmis or blank.

COPYTODEMANDER cannot be used with GROUP.

Only one NEWDEMANDERIDVARS may be specified if COPYTODEMANDER is used.  
None of the metadata such as variable and value labels is copied.  Use APPLY DICTIONARY 
to bring over variable properties.

If DS3 is specified, a new dataset is created containing the cases in the supplier dataset actually 
used for the matches.  It will be the active dataset after the command is run.  
DS3 cannot be used with GROUP.

(This implies that any unnamed dataset will be closed.)
It contains all the variables froom the supplier dataset plus the MATCHGROUPVAR.
If DEMANDERID is specified, it also contains the ID variable from the demander dataset.  These 
variable names must all be unique.
DS3 is only a dataset: use the SAVE command to turn it into a file.

DRAWPOOLSIZE can name a variable for the demander dataset that will record the
number of cases in the supplier dataset that are eligible to match the demander case.
This can be useful in identifying the types of cases in terms of BY variables where
the supplier pool is thin.  The variable must not already exist in the demander dataset.

By default, sampling from the supplier dataset is done without replacement.  Specify
SAMPLEWITHREPLACEMENT=TRUE to sample with replacement.

By default, memory usage is minimized in picking supplier dataset candidate match cases
(all eligible cases have an equal probability of selection).  This requires an extra data pass.  If
the possible number of matching cases for a demander case is small or the supplier dataset is
not large, specifying
MINIMIZEMEMORY=FALSE may improve performance by eliminating the extra data pass.  In the
case of 1-1 matching, this is recommended.
MINIMIZEMEMORY=TRUE cannot be combined with EXACTPRIORITY=TRUE.

When MINIMIZEMEMORY=TRUE, each supplier case is eligible for assignment at random 
to just one demander case for which it is within tolerance.  When FALSE, the case is 
eligible for all cases within the tolerance, and one is picked at random from all of those.
This means that when TRUE, a usually small number of demander cases may go unmatched
when a match could have been found, but when FALSE, the matching tables can become
very large, especially in the PSM case.

By default, cases in the demander dataset are processed in case order.  If there are insufficient 
supplier cases, you may specify SHUFFLE=TRUE to process the demander cases in random order.
This ensures that earlier cases do not have an advantage over later ones in matching.  
SHUFFLE increases the memory requirement and will take longer to execute.

Use SEED=number to set the random number generator to a known state for repeatability.

Matching can be quite time consuming.  Progress can be logged to a file during the run.
Specify a file/path as LOGFILE="filespec" to record progress.
If LOGACCESSMODE is OVERWRITE, each run overwrites an existing file.  APPEND
appends to the log file.
The contents record the state the process has reached and writes the number of operations
completed at 1000 or 5000 case intervals for some operations.

FUZZY /HELP.
prints this output and does nothing else.

Example:
FUZZY DEMANDERDS=demander SUPPLIERDS=supplier
BY=origin cylinder SUPPLIERID=id
NEWDEMANDERIDVARS=matchedcaseid
COPYTODEMANDER=mpg randomnumber randomstring
DS3=dsextra DEMANDERID=demanderid.
"""

#def xRun():
def Run(args):
    """Run the casectrl function as SPSS syntax"""
    
    ###print args   #debug
    ###args = xargs
    args = args[list(args.keys())[0]]
    
    oobj = Syntax([
    Template("DEMANDERDS", subc="", var="demanderds", ktype="varname"),
    Template("SUPPLIERDS", subc="", var="supplierds", ktype="varname"),
    Template("DS3", subc="", var="ds3", ktype="varname"),
    Template("BY", subc="", var="by", ktype="varname", islist=True),
    Template("FUZZ", subc="", var="fuzz", ktype="float", islist=True),
    Template("EXACTPRIORITY", subc="", var="exactpriority", ktype="bool"),
    Template("BEST", subc="", var="best", ktype="str",
        vallist=["propor", "abs", "squared"]),
    Template("CUSTOMFUZZ", subc="", var="customfuzz", ktype="literal"),
    Template("GROUP", subc="", var="group", ktype="existingvarlist", islist=False),
    Template("SUPPLIERID", subc="", var="supplierid", ktype="varname"),
    Template("NEWDEMANDERIDVARS", subc="", var="matchslots", islist=True),
    Template("COPYTODEMANDER", subc="", ktype="varname",var="copytodemander", islist=True),
    Template("MATCHGROUPVAR", subc="", var="hashvar", ktype="varname"),
    Template("DRAWPOOLSIZE", subc="", var="drawpool", ktype="varname"),
    Template("DEMANDERID", subc="", var="demanderid", ktype="varname"),
    
    Template("SAMPLEWITHREPLACEMENT", subc="OPTIONS", var="samplewithreplacement", ktype="bool"),
    Template("MINIMIZEMEMORY", subc="OPTIONS", var="minimizememory",  ktype="bool"),
    Template("SEED", subc="OPTIONS", var="seed", ktype="int",vallist=(-2**31+1, 2**31-1)),
    Template("SHUFFLE", subc="OPTIONS", var="shuffle", ktype="bool"),
    Template("MAXQUEUE", subc="OPTIONS", ktype="float", var="maxqueue",
        vallist=[.01, 1.0]), 
    Template("LOGFILE", subc="OUTFILE", var="logfile", ktype="literal"),
    Template("ACCESSMODE", subc="OUTFILE", var="logaccessmode", ktype="str", vallist=("append", "overwrite"))
    ])

    #enable localization
    global _
    try:
        _("---")
    except:
        def _(msg):
            return msg

    if "HELP" in args:
        #print helptext
        helper()
    else:
        processcmd(oobj, args, casecontrol, vardict=spssaux.VariableDict())

#import cProfile

#def Run(args):
    #global xargs
    #xargs = args
    #cProfile.run("FUZZY.xRun()", "c:/users/fuzzy/profile")

class DataStep(object):
    def __enter__(self):
        """initialization for with statement"""
        try:
            spss.StartDataStep()
        except:
            spss.Submit("EXECUTE")
            spss.StartDataStep()
        return self

    def __exit__(self, type, value, tb):
        spss.EndDataStep()
        return False

def casecontrol(by, supplierid, matchslots, demanderds=None, supplierds=None, group=None,
                copytodemander=[], ds3=None,  demanderid=None, samplewithreplacement=False,
                hashvar="matchgroup", seed=None, shuffle=False, minimizememory=False,
                fuzz=None, exactpriority=True, drawpool=None, customfuzz=None, best="propor", 
                maxqueue=1.0, logfile=None, logaccessmode="overwrite"):
    """Find match for demanderds cases in supplierds and add identifiers to demanderds.  Return unmatched count. 
    
    demanderds is the dataset name of cases needing a match (demanders)
    supplierds is the dataset name of cases supplying matches (suppliers)
    ds3 is optional and will contain the supplierds cases used for matches.
    demanderid is optional.  If specified, and ds3 is used, it will be appended to the supplier cases.  It must have a name
    different from any variable in the supplier dataset.
    
    by is a variable or sequence of variable names used to determine a match.  The variables must exist in both demanderds and supplierds.
    supplierid is the variable name of the ID variable in the supplier dataset.
    matchslots is the variable name or sequence of variable names for the ids of the matches
    
    copytodemander is an optional list of variables in supplierds to be added to demanderds.  If this option is used, only a single
    matching case can be requested.  Variable types must agree for variables that already exist in demanderds.
    samplewithreplacement, if true, samples with replacement; otherwise sampling is without replacement.
    hashvar is an optional variable name to contain the hash of the match variables and added to demanderds and ds3.
    If seed is not None, its value is used to initialize the generator for repeatability.
    If shuffle is True, the demander cases are matched in a random order; otherwise they are matched in case order.
    Since shuffling requires O(N) memory and will be slower, presorting the demander dataset by a random number is an alternative.
    If minimizememory is true, only one eligible case is assigned to eachdemander, and the available matches table is suppressed.
    If fuzz is not None, it must be a sequence of half-ranges, one per by variable.  Use 0 for any nonnumeric variables.
    If fuzz is None, matches must be exact on all matching variables.
    By default, with fuzzy matching, exact matches take priority when available except with minimizememory.  
    Set exactpriority False to treat all equally.
    best specifies whether differences are computed as absolute value or squared diff
    Minimize memory cannot be used with exactpriority.
    drawpool names a variable to be created in the demander ds whose value is the size of the pool for
    each case
"""
    global logger   # logging object
    # debugging
    #try:
        #import wingdbstub
        #import threading
        #wingdbstub.Ensure()
        #wingdbstub.debugger.SetDebugThreads({threading.get_ident(): 1})
    #except:
        #pass

    if not seed is None:
        random.seed(seed)

    # minimizememory no longer supported 3/2023
    minimizememory = False
    myenc = locale.getlocale()[1]  # get current encoding in case conversions needed
    by = spssaux._buildvarlist(by)
    matchslots = spssaux._buildvarlist(matchslots)
    nmatches = len(matchslots)  # number of matches requested
    if group:
        activedsname = spss.ActiveDataset()
        if demanderds is None:
            demanderds = activedsname
        if supplierds is None:
            supplierds = activedsname
    else:
        if demanderds is None or supplierds is None:
            raise ValueError(_("""The required demander or supplier dataset name was not specified"""))
    if demanderds == supplierds and not group:
        raise ValueError(_("""A group variable must be specified if the demander and supplier datasets are the same"""))
    if group and demanderds != supplierds:
        raise ValueError(_("""A group variable cannot be used unless the demander and supplier datasets are the same"""))
    if group and copytodemander:
            raise ValueError(_("""COPYTODEMANDER cannot be used with GROUP"""))
    copytodemander = spssaux._buildvarlist(copytodemander)
    if nmatches > 1 and len(copytodemander) > 0:
        raise ValueError(_("Error: variables can only be copied to the demander dataset if only a single match is requested"))

    if len(set([v.lower() for v in matchslots])) != nmatches or nmatches == 0:
        matchslots = ", ".join(matchslots)
        if not isinstance(matchslots, str):
            matchslots = str(matchslots, myenc)
        raise ValueError(_("Match id variable names are not unique or none was specified\n") + matchslots)

    if fuzz is not None and len(fuzz) != len(by):
        raise ValueError(_("List of fuzz values does not match list of BY variables.  Fuzz: %s") % fuzz)

    if fuzz and exactpriority:
        if minimizememory:
            # not translated
            print("Fuzzy matching with exactpriority cannot be combined with minimizememory.  Setting minimizememory to NO.")
        mimimizememory = False
    if minimizememory and samplewithreplacement:
        print(_("""Samping with replacement cannot be used with minimize memory.  Using sampling without replacement"""))
        samplewithreplacement = False

    nomatchcount = 0

    with DataStep():
        try:
            demanderdsx = spss.Dataset(demanderds)
        except:
            raise ValueError(_("Cannot access specified demander dataset"))
        if demanderds != supplierds:
            try:
                supplierds = spss.Dataset(supplierds)
            except:
                raise ValueError(_("Cannot access specified supplier data"))
        else:
            supplierds = demanderdsx
        demanderds = demanderdsx
        # drawpool variable must precede hashvar, because multiple hash variables may be written
        if drawpool:
            demanderds.varlist.append(drawpool)
            drawpoolindex = demanderds.varlist[drawpool].index
        else:
            drawpoolindex = None

        demanderds.varlist.append("matchdiff_")   # variable for diff between case and control.
        matchdiffindex = demanderds.varlist["matchdiff_"].index    # where difference variables start
        demanderds.varlist.append(hashvar)
        hashvarindex = demanderds.varlist[hashvar].index

        try:
            supplieridindex = supplierds.varlist[supplierid].index
            idtype= supplierds.varlist[supplierid].type
        except:
            if not isinstance(supplierid, str):
                supplierid = str(supplierid, myenc)
            raise ValueError(_("Supplier dataset id variable not found: %s") % supplierid)
        for v in matchslots:
            demanderds.varlist.append(v, idtype)
        if ds3:
            dsextra = spss.Dataset(name=None)
            dsextraname = dsextra.name
            lends3 = createds3(supplierds, dsextra, hashvar, demanderds, demanderid, supplierid, myenc, group, drawpool)
        else:
            dsextra = None
            lends3 = 0
        if demanderid is not None:
            demanderidindex = demanderds.varlist[demanderid].index
        else:
            demanderidindex = None
        if group:
            groupindex = demanderds.varlist[group].index
        else:
            groupindex = None

        # create new variables and warn if type mismatch for existing variables.  No metadata is copied.
        demandercopyindexes = []
        suppliercopyindexes = []
        copyvartypes = []
        typeconflicts = []
        if copytodemander:
            demandervars = set([v.name for v in demanderds.varlist])  # set of demander variable names
            svtype = 0
            for sv in copytodemander:
                try:
                    svtype = supplierds.varlist[sv].type   # will cause exception if variable does not exist in supplierds
                except:
                    if not isinstance(sv, str):
                        sv = str(sv, myenc)
                        raise ValueError(_("Supplier dataset variable not found: %s") % sv)
                if not sv in demandervars:
                    demanderds.varlist.append(sv, svtype)
                else:
                    if demanderds.varlist[sv].type != svtype:
                        typeconflicts.append(sv)
                demandercopyindexes.append(demanderds.varlist[sv].index)
                suppliercopyindexes.append(supplierds.varlist[sv].index)
                copyvartypes.append(svtype)
            if typeconflicts:
                typeconflicts = ",".join(typeconflicts)
                if not isinstance(typeconflicts, str):
                    typeconflicts = str(typeconflicts, myenc)
                raise ValueError(_("Error: supplier/demander type conflicts exist for variables: ") + typeconflicts)

        matcher = Matcher(by, supplierid, demanderds, supplierds, nmatches, samplewithreplacement,
            minimizememory, fuzz, exactpriority, groupindex, customfuzz, best, matchdiffindex, maxqueue)

        # First pass the demander dataset to establish all required matches.  
        # If minimizing memory, pass the supplier dataset to count cases for each required key.
        # Then pass the supplier dataset to develop the candidates.  If minimizing memory, only as many
        # suppliers will be recorded for a key as needed with all eligible cases given equal probability of selection.
        # Finally pass the demander dataset and harvest the matches.

        demanderdscases = demanderds.cases
        supplierdscases = supplierds.cases

        demanderdssize = len(demanderdscases)
        supplierdssize = len(supplierdscases)

        logger = Logger(logfile=logfile, accessmode=logaccessmode)

        logger.info("Adding demanders")
        addcount = 0
        for i in range(demanderdssize):
            if i%5000 == 4999:
                logger.info("Cumulative demanders added = %s" % addcount)
            addcount += matcher.adddemander(demanderdscases[i])
        logger.info("Done adding demanders.  Number added = %s" % addcount)
        
        if addcount == 0:
            raise ValueError(_("There are no demander cases.  Check the input dataset or group indicator"))
        matcher.setSafetyValve()

        logger.info("Adding suppliers.  suppliersize = %s (for single dataset usage, this is the total casecount)" % supplierdssize)
        addcount = 0
        matchmaker = Matchmaker(demanderdscases, matcher, hashvarindex, supplierdscases, dsextra,
            demandercopyindexes, suppliercopyindexes, demanderidindex, drawpoolindex, supplieridindex, group, matchdiffindex)
        matcher.domatch = matchmaker.do
        for i in range(supplierdssize):
            if i%1000 == 999:
                logger.info("Cumulative potential suppliers processed = %s.  Supplier adds = %s" % (i,addcount))
            addcount += matcher.addsupplier(supplierdscases[i], i)
        logger.info("Done adding suppliers.  Number added: %s.  A supplier may be added to more than one demander." % addcount)

        logger.info("Making matches.  Demandersize = %s" % demanderdssize)

        if not shuffle:
            for i in range(demanderdssize):
                if i % 1000 == 999:
                    logger.info("Cumulative matches = %s, nomatch Count = %s" % (i, nomatchcount))
                nomatchcount += matchmaker.do(i)
        else:
            caselist = list(range(demanderdssize))
            random.shuffle(caselist)
            for i in caselist:
                if i%1000 == 999:
                    logger.info("Cumulative matches = %s, nomatch count = %s" % (i,  nomatchcount))
                nomatchcount += matchmaker.do(i)
        logger.info("Done matching.  Displaying results")

    if ds3:
        spss.Submit(r"""DATASET ACTIVATE %(dsextraname)s.
        DATASET NAME %(ds3)s""" % locals())

    StartProcedure(_("Case-control matching"), "SPSSINC CASECTRL")

    tbl = spss.BasePivotTable(_("Case Control Matching Statistics"), "CASECTRLSTATS")
    tbl.SetDefaultFormatSpec(spss.FormatSpec.Count)
    rowlabels = [_("Demander Cases"), _("Supplier Cases"), _("Matches"), _("Unmatched"),
        _("""Sampling"""), _("""Log file"""), _("Demander Queue Limit")]
    cells = [matcher.demandercountin] + [matcher.suppliercountin] + matcher.counts +\
    [samplewithreplacement and _("with replacement") or _("without replacement")] +\
        [(logfile is None and _("""none""")) or logfile] + [matcher.safetyValve]
    tbl.TitleFootnotes(_(f"""Match variables: {" ".join(by)}"""))
    tbl.SimplePivotTable(rowdim = _("Match Type"),
        rowlabels=rowlabels,
        coldim="",
        collabels = [_("Count")],
        cells = cells)
    if fuzz:
        by.insert(0, _("Exact (All Variables)"))
        fuzz.insert(0, None)
        for i in range(len(fuzz)):
            if matcher.tries[i] > 0.:
                matcher.rejections[i] = float(matcher.rejections[i]) / matcher.tries[i] * 100.
        tblvalues = [(fuzz[i], matcher.tries[i], matcher.rejections[i]) for i in range(len(fuzz))]
        collabels = [_("Value"), _("Fuzzy Match Tries"), _("Incremental Rejection Percentage")]
        caption = _("Tries is the number of match comparisons before drawing.  \
Rejection percentage shows the match rejection rate.  \
Rejections are attributed to the first variable in the BY list that causes rejection.")
    elif customfuzz:
        tblvalues = len(by) * [None]
        collabels = [_("Value")]
        caption = _("""Case distance computed from custom function: %s""" % customfuzz)
    else:
        tblvalues = len(by) * [0]
        collabels = [_("Value")]
        caption = ""
    fuzztbl = spss.BasePivotTable(_("Case Control Match Tolerances"), "CASECTRLFUZZ", caption=caption)
    fuzztbl.SimplePivotTable(rowdim=_("Match Variables"),
        rowlabels=by,
        coldim="",
        collabels=collabels,
        cells = tblvalues)
    if not minimizememory:
        matcher.freqs.showtable()
    spss.EndProcedure()
    logger.done()

    return nomatchcount


def createds3(dsin, dsout, hashvar, demanderds, demanderid, supplierid, myenc, group, drawpool):
    """Create a new dataset by copying the variables in dsin to dsout.  No cases are created.
    Return number of variables in dsout.
    
    dsin is the intput dataset; dsout is the output dataset.
    hashvar is the name of the hash variable.
    if demanderid is not None, its definition from demanderds is appended to dsout.
    If using group, the demanderid name is suffixed with "_", since it would always duplicate
    the supplierid name."""

    for v in dsin.varlist:
        if v.name != drawpool:
            dsout.varlist.append(v.name, v.type)

    # ugly!
    unicodemode = isinstance(dsout.varlist[0].name, str)
    if unicodemode and not isinstance(hashvar, str):
        hashvar = str(hashvar, myenc)
    if demanderid is not None and unicodemode and not isinstance(demanderid, str):
        demanderid = str(demanderid, myenc)

    if hashvar not in [v.name for v in dsout.varlist]:
        dsout.varlist.append(hashvar, 0)

    if demanderid is not None and demanderid not in [v.name for v in dsout.varlist]:
        try:
            dsout.varlist.append(demanderid, demanderds.varlist[demanderid].type)
        except:
            if not isinstance(demanderid, str):
                demanderid = str(demanderid, myenc)
            raise ValueError(_("Demander id variable not found, or it duplicates a name in the supplier dataset: %s") % demanderid)
    return len(dsout.varlist)

class Matchmaker(object):
    """Use the Matcher class data structures to draw matches and propagate data as required"""

    def __init__(self, demanderdscases, matcher, hashvarindex, supplierdscases, ds3cases,
                 demandercopyindexes, suppliercopyindexes,
                 demanderidindex, drawpoolindex, supplieridindex, group, matchdiffindex):
        """demanderdscases is the demander case to match.
        matcher is the Matcher object to use.
        hashvarindex is the variable index for the hash value variable.  The matches are written to following contiguous variables.
        demandercopyindexes and suppliercopyindexes are case indexes for copying values from supplierds to demanderds
        Only one match is allowed if copying.
        If there is no match, values of existing variables are not changed.
        
        If ds3cases is not None, supplier dataset cases used are written to ds3cases
        if demanderidindex is not None and ds3 is being created, its value is copied to ds3."""

        attributesFromDict(locals())

    def do(self, casenumber):
        """draw match(es) for case casenumber and propagate values as required"""

        if self.matcher.groupindex != None and self.demanderdscases[casenumber][self.matcher.groupindex] != 1:
            return 0

        hash, matches, drawpoolsize, matchdiff = self.matcher.draw(self.demanderdscases[casenumber], self.supplierdscases)  # 3/1
        self.demanderdscases[casenumber, self.hashvarindex] = hash
        diffs = [item for item in matchdiff if item is not None]
        if diffs:
            meandiff = sum(diffs) / len(diffs)
        else:
            meandiff = None     
        self.demanderdscases[casenumber, self.matchdiffindex] = meandiff
        if self.drawpoolindex:
            self.demanderdscases[casenumber, self.drawpoolindex] = drawpoolsize
        
  
        for m in range(len(matches)):
            casenum = matches[m]    # case number of the supplier dataset
            if casenum is not None:
                suppid = self.supplierdscases[matches[m], self.supplieridindex]
                self.demanderdscases[casenumber, self.hashvarindex + 1 + m] = suppid    # was 1
                for dv, sv in zip(self.demandercopyindexes, self.suppliercopyindexes):
                    self.demanderdscases[casenumber,dv] = self.supplierdscases[casenum, sv]

            # ds3 will contain the complete supplier case + hash value + optional demanderid
            if self.ds3cases:
                if casenum is not None:
                    self.ds3cases.cases.append(self.supplierdscases[casenum])
                    if self.group:
                        self.ds3cases.cases[-1, -2] = hash
                        self.ds3cases.cases[-1, -1] = self.demanderdscases[casenumber, self.supplieridindex]
                    else:
                        if self.demanderidindex is not None:
                            self.ds3cases.cases[-1, -2] = hash
                            self.ds3cases.cases[-1, -1] = self.demanderdscases[casenumber, self.demanderidindex]
                        else:
                            self.ds3cases.cases[-1, -1] = hash

        # return count of unmatched demands where demander by do not have missing or blank
        if hash is None:
            return 0
        else:
            return matches.count((None, None))

class Matcher(object):
    """Build, maintain, and draw from hash lists for cases"""

    def __init__(self, by, supplierid, demanderds, supplierds, nmatches, samplewithreplacement, minimizememory,
        fuzz, exactpriority, groupindex, customfuzz, best, matchdiffindex, maxqueue):
        """by is a variable or list of variables to match on.
        supplierid is the id variable name in the supplier dataset.
        demanderds and supplierds are the demander and supplier datasets.
        nmatches is the number of matches requested for each demander.
        samplewithreplacement indicates sampling with or without replacement.
        If minimizememory is True, an extra data pass is required but memory usage for the supplier set is reduced.
        fuzz is a sequence of fuzz factors, one for each by variable.  If the variable is not numeric, fuzz must be zero.

        
        A DataStep is expected to be active for this class."""

        """The demander object is a dictionary whose keys are the hash of the by variable(s).
        The values are lists of matching suppliers with each list item being a duple (casenumber, idvalue)"""
        self.demanders = {}
        self.demanderbys = {}
        # The following two dictionaries are used only if minimizememory is True
        self.demandercount = {}  # count of demanders for each key
        self.suppliercount = {}     # count of suppliers for each key
        self.groupindex = groupindex

        self.demandervars = self.buildvars(demanderds, by)  # indexes of demander match variables
        self.nvars = len(self.demandervars)
        self.demanderscopy = set()   # disposable copy of demander hashes
        self.suppliervars = self.buildvars(supplierds, by)      # indexes of supplier match variables (same names but could be different indexes)
        self.samplewithreplacement=samplewithreplacement
        self.demanderds = demanderds
        self.supplierds = supplierds
        self.supplierid = self.buildvars(supplierds, [supplierid])[0]   # index of id variable in supplier dataset
        self.nmatches = nmatches
        self.minimizememory = minimizememory
        self.fuzz = fuzz
        if customfuzz:
            customparts = customfuzz.split(".")
            __import__(customparts[0])
            self.customfuzz = getattr(sys.modules[customparts[0]], customparts[1])
        else:
            self.customfuzz = None
        self.best = best
        self.maxqueue = maxqueue

        # if fuzzy matching, keep count of tries incremental rejections overall and by variable
        if fuzz:
            self.tries = dict((i,0) for i in range(len(fuzz)+1))
            self.rejections = dict((i, 0) for i in range(len(fuzz)+1))
        elif customfuzz:
            self.tries = {0:0}
            self.rejections = {0:0}
        self.freqs = Freqs()
        self.bys = {}                     # holds demander key variables for use in fuzzy match calculations
        self.exactcount = {}         # used in fuzzy matching to give priority to exact matches
        self.counts=[0,0]          # counts of exact, fuzzy, and unmatched cases
        self.usedsuppliers = set() # for sample wout replacement, tracks supplier cases used (case number)
        self.demandercountin = 0
        self.suppliercountin = 0
        
    def setSafetyValve(self):
        # Set limit on number of suppliers to add to a demander based on worst case inputs
        # but allow user to scale it down
        raw = max(1, round((self.demandercountin * self.nmatches + 1) * self.maxqueue))
        self.safetyValve = max(raw, 5)

    def adddemander(self, case):
        """Add a demander.  Return 0 or 1 for whether added or not"""

        if self.groupindex != None and case[self.groupindex] != 1:
            return 0
        self.demandercountin += 1
        h, keyvalues = self.hash(self.demandervars, case)
        if h is not None and not h in self.demanders:
            self.demanders[h] = []
            if self.fuzz or self.customfuzz:
                self.bys[h] = keyvalues
        #if self.minimizememory and h is not None:
            #self.demandercount[h] = self.demandercount.get(h, 0) + self.nmatches  # 5/28/09
            #self.demanderscopy.add(h)
        return 1

    #def countsuppliers(self, case):
        #"""If minimizing memory, count suppliers for this key.
        #This can be very timeconsuming if using fuzzy matching.

        #case is a supplier case.
        #This routine should not be called unless minimizememory is True"""

        ##if self.fuzz:
        ##    h = self.fuzzhash(self.suppliervars, case, self.demanders.get(dhash, None))
        #if self.groupindex != None and case[self.groupindex] != 0:
            #return
        #if not (self.fuzz or self.customfuzz):
            #h, values = self.hash(self.suppliervars, case)
            #if h in self.demanders:
                #self.suppliercount[h] = self.suppliercount.get(h, 0) + 1
        #else:
            #for h in self.demanders:
                #hh = self.rehash(h, case)
                #if hh > 0:
                    #self.suppliercount[h] = self.suppliercount.get(h, 0) + 1

    def addsupplier(self,  case, casenum):
        """Add a supplier.  If no demander for this case, do nothing.
        
        case is the current supplier case, casenum is its case number saved for later use.
"""
        if self.groupindex != None and case[self.groupindex] != 0:
            return 0
        self.suppliercountin += 1
        takecount = 0
        hlist = []
        if not (self.fuzz or self.customfuzz):   # no fuzz, so exact match required
            h, values = self.hash(self.suppliervars, case)
            if h in self.demanders:   # a demander case has the same hash, i.e., match
                self.demanders[h].append(Supp(casenum, 0, case[self.supplierid]))
                if len(self.demanders[h]) > self.safetyValve:
                    self.demanders[h].pop()
                takecount += 1

        # there is a fuzz specification or custom fuzz function
        else:
            demanders = self.demanders
            for h in self.demanders:
                matchlevel, code =  self.rehash(h, case)
                if matchlevel == 0:
                    continue
                if matchlevel == 2:    # exact match.  Put at head of list and increment count
                    self.demanders[h].insert(0, Supp(casenum, 0, case[self.supplierid]))
                else:
                    bisect.insort(self.demanders[h], Supp(casenum, code, case[self.supplierid]))
                if len(self.demanders[h]) > self.safetyValve:
                    self.demanders[h].pop()                 
                takecount += 1

        return takecount

    def rehash(self, h, case):
        """Test supplier case against demander case allowing for fuzzy matching.
        
        h is the current demander case hash
        case is the current supplier case
        return is 
        -  0 if no match
        -  1 if fuzzy match
        -  2 if exact match
        + sum absolute or squared diff if fuzzy, else 0
        """

        hh, values = self.hash(self.suppliervars, case)   # first see if exact match, i.e., match vars are identical
        self.tries[0] += 1
        if hh == h:
            return 2, 0   # exact indicator, difference score
        else:
            self.rejections[0] += 1
        dcase = self.bys[h]
        cumdiff = 0
        if self.customfuzz:
            # function takes two lists and should return 0 or 1,
            # but a 2 could be used to prioritize a nonexact match
            result = self.customfuzz(dcase, [case[i] for i in self.suppliervars])
            if result == 0:
                return result, 0
        else:
            result = 1  # fuzzy match.  Calculate match difference
        # calculate match quality
        # fuzz  limits apply even with a custom function
        for i, fuzz in enumerate(self.fuzz):
            self.tries[i+1] += 1
            # place to allow for custom matching calculator
            # diff returns absolute difference between a demander and suplier match variable
            ccdiff =  diff(dcase[i], case[self.suppliervars[i]])
            if not ccdiff <= fuzz:
                self.rejections[i+1] += 1  # count first variable causing rejection
                result = 0  # 0,0  no match
                break
            if self.best == "squared":
                cumdiff += ccdiff ** 2
            elif self.best == "abs":
                cumdiff += ccdiff
            else:
                if ccdiff > 0:
                    cumdiff += ccdiff / (abs(dcase[i]) + abs(case[self.suppliervars[i]]))
        cumdiff = cumdiff / self.nvars
        return result, cumdiff

    def filteredlist(self, h):
        """Return the list of potential suppliers
        
        h is the demander hash
        If samplewithreplacement is False, any suppliers already used are removed and the exactcount
        field is adjusted"""

        thelist = self.demanders.get(h, ()) #initial list not accounting for suppliers used for other demanders
        if self.samplewithreplacement:
            return thelist

        exactcount = self.exactcount.get(h, 0)
        lenthelist = len(thelist)
        for j in range(lenthelist, 0, -1):
            i = j - 1
            #casenum, diff, hh = thelist[i]
            if thelist[i].casenum in self.usedsuppliers:
                thelist.pop(i)
                if i < exactcount:
                    self.exactcount[h] -= 1
        return thelist

    def draw(self, case, supplierdscases):    #3/1/11
        """Try to draw matches for demander case case.
        
        Return a list of nmatches match ids preceded by the hash value.  If no match is possible, None is returned for each.
        If the case is missing any match variable, no matches will be drawn.
        """

        if self.groupindex != None and case[self.groupindex] != 1:
            #h, draws, initiallistsize, matchdiff
            return None, [(None, None)], None
        h, values = self.hash(self.demandervars, case)
        # get eligibles.  If sampling without replacement, previously used cases are removed.
        thelist = self.filteredlist(h)
        draws = []
        initiallistsize = len(thelist)  # tallying only for full list.  If multiple draws requested per case, actual would shrink
        self.freqs.accumulate(initiallistsize)

        matchdiff = []
        for i in range(self.nmatches):
            scase, diff = self.picker(thelist)
            draws.append(scase)
            matchdiff.append(diff)
            ###print(scase, diff)   #debug

        return h, draws, initiallistsize, matchdiff

    def picker(self, thelist):
        """Find a supplier match and return its casenum and diff
        
        thelist is the unpruned list of eligibles, so it may contain used cases
        listsize is its length"""
        
        listsize = len(thelist)
        startat = 0
        while True:
            # find first (smallest) unused eligible case
            for i in range(listsize):
                if not thelist[i].casenum in self.usedsuppliers:
                    startat = i
                    break
            else:      # no unused cases
                self.counts[1] += 1
                return None, None
            
            # find the cases with the same diff.  The first case will always qualify
            testvalue = thelist[startat].diff
            for j in range(startat, listsize):
                if thelist[j].diff != testvalue:
                    endat = j
                    break
            else:
                endat = listsize
                
            # try to pick a supplier case at random
            # there must always be at least one case in the group.
            if self.samplewithreplacement:
                choiceindex = random.randint(startat, endat)
                draw = thelist[choiceindex]
            else:
                # draw until an unused case is found or no more cases in this diff group
                while startat <= endat:
                    choiceindex = random.randint(startat, endat-1)
                    draw =  thelist.pop(choiceindex)
                    if not draw.casenum in self.usedsuppliers:
                        self.usedsuppliers.add(draw.casenum)  # add case number to used set                
                        break
                    else:
                        draw = None
                    endat -= 1
            if draw:
                break
            startat = endat   # move up to next diff level
        else:
            # no suppliers available
            self.counts[1] += 1
            return None, None
        
        self.counts[0] += 1
        return draw.casenum, draw.diff

       

    def hash(self, indexes, case):
        """Return a hash of the case according to the indexes in the indexes tuple and the key values.
        
        If any value in the index is None or, for strings, blank, the result is None, None
        indexes is the list of indexes into the case vector"""

        keys = tuple([case[v] for v in indexes])
        for v in keys:
            if isinstance(v, str):
                if v.rstrip() == "":
                    return None, None
            else:
                if v is None:
                    return None, None

        return hash(keys), keys  # keys for fuzzy matching

    def buildvars(self, ds, by):
        """return a tuple of variable indexes for by.
        
        ds is the dataset.
        by is a sequence of variables for matching"""

        try:
            return tuple([ds.varlist[v].index for v in by])
        except:
            raise ValueError(_("Undefined variable in BY list: %s") % v)

class Freqs(object):
    def __init__(self):
        self.drawcount = 0
        self.sum = 0
        self.bucket = dict([(i,0) for i in range (13)])

    def accumulate(self, listsize):
        # maintain the distribution of cases to draw from
        self.drawcount +=1
        self.sum += listsize
        if listsize == 0:
            bucket = 0
        elif listsize == 1:
            bucket = 1
        else:
            bucket = min((listsize + 9)//10 + 1, 12)
        self.bucket[bucket] += 1

    def showtable(self):
        tbl = spss.BasePivotTable(_("Distribution of Available Matches"), "CASECTRLAVAIL",
            caption = _("Average matching cases available: %.2f") % (float(self.sum)/self.drawcount))
        tbl.SetDefaultFormatSpec(spss.FormatSpec.Count)
        # thirteen total buckets
        rowlabels = ["0", "1", "2 - 10"]
        for i in range(11, 100, 10):
            rowlabels.append(str(i) + " - " + str(i + 9))
        rowlabels.append("> 100")
        cells = sorted(self.bucket.items())
        cells = [val for key, val in cells]
        tbl.SimplePivotTable(rowdim = _("Count"),
            rowlabels=rowlabels,
            coldim="",
            collabels = [_("Count")],
            cells = cells)

def diff(x, y):
    """Return absolute difference between x and y, assumed to be of the same basic type
    
    if numeric and neither is missing (None), return ordinary absolute value
    if not numeric, return 0 if identical and not blank.
    Otherwise return BIG."""

    BIG = 1e100

    try:
        return abs(x - y)
    except:
        if isinstance(x, str):
            x = x.rstrip()
            y = y.rstrip()
            if x == y and x != "":
                return 0
        return BIG


def attributesFromDict(d):
    """build self attributes from a dictionary d."""

    # based on Python Cookbook, 2nd edition 6.18

    self = d.pop('self')
    for name, value in d.items():
        setattr(self, name, value)


def StartProcedure(procname, omsid):
    """Start a procedure
    
    procname is the name that will appear in the Viewer outline.  It may be translated
    omsid is the OMS procedure identifier and should not be translated.
    
    Statistics versions prior to 19 support only a single term used for both purposes.
    For those versions, the omsid will be use for the procedure name.
    
    While the spss.StartProcedure function accepts the one argument, this function
    requires both."""

    try:
        spss.StartProcedure(procname, omsid)
    except TypeError:  #older version
        spss.StartProcedure(omsid)

class Logger(object):
    """Manage logging"""
    def __init__(self, logfile, accessmode):
        """Enable logging
        
        logfile is the path and name for the log file or None
        accessmode is "overwrite" or "append" """

        self.logfile = logfile
        if logfile is not None:
            filemode = accessmode == "overwrite" and "w" or "a"
            logging.basicConfig(filename=logfile, level=logging.INFO, filemode=filemode,
                format="%(asctime)s: %(message)s", datefmt="%H:%M:%S")
            logging.info("Run started: %s" % time.asctime())
            self.starttime = time.time()   # start time as seconds

    def info(self, message):
        """Add message to the log if logging"""

        if self.logfile:
            logging.info(message)

    def done(self):
        if self.logfile:
            logging.info("Run ended.  Elapsed time (minutes) = %.3f", (time.time() - self.starttime)/60)
            logging.shutdown()

def helper():
    """open html help in default browser window
    
    The location is computed from the current module name"""

    import webbrowser, os.path

    path = os.path.splitext(__file__)[0]
    helpspec = "file://" + path + os.path.sep + \
         "markdown.html"

    # webbrowser.open seems not to work well
    browser = webbrowser.get()
    if not browser.open_new(helpspec):
        print(("Help file not found:" + helpspec))
try:    #override
    from extension import helper
except:
    pass