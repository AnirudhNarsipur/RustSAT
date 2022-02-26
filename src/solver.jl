module MainModule
include("./dimacparser.jl")


const aBad = Bad()
#Check if any of the assigments are in state st
function literalInState(ls::Vector{AbstractAssignment}, st::AbstractAssignment)
    for elem in ls
        if elem == st
            return true

        end
    end
    return false
end
# Check the assigment of a literal
function checkAssignment(assigments::Dict{T,LiteralState}, literal::Number) where {T<:Number}
    as = assigments[abs(literal)]
    if (literal < 0 && as == Negative) || (literal > 0 && as == Positive)
        return Satisfied
    elseif as == Unset
        return Undecided
    else
        return Conflict
    end
end
# Add decision to the stack
function updateStack(inst::SATInstance, literal::Number)
    inst.varAssignment[abs(literal)] = (literal > 0) ? Positive : Negative
    push2DElem(inst.decisionStack, convert(inst.usignedtp, abs(literal)))
    return nothing
end
# Add new Stack element for new decision level
function newStackCall(inst::SATInstance)
    pushElem(inst.decisionStack, initializeDynamicVec(inst.usignedtp))
end
# Pop Elements from stack and undo the decisions
function unwindStack(inst::SATInstance)
    last = pop2DElem(inst.decisionStack)
    if last isa Bad
        return nothing
    elseif last isa Some
        for i in last.value
            inst.varAssignment[i] = Unset
        end
        return nothing
    else
        error("unreachable!")
    end
end

# Assign a variable to the state of a literal
# Given setAssignment(inst,-3) -> updates 3 to Negative
function setAssignment(inst::SATInstance, literal::Number)
    curr = checkAssignment(inst.varAssignment, literal)
    if curr == Satisfied
        None()
    elseif curr == Conflict
        Bad()
    elseif curr == Undecided
        updateStack(inst, literal)
        return None()
    else
        error("should not be reached")
    end
end
# Returns a function that checks the watched literals of a clause
function checkWatchers(inst::SATInstance) where {T}
    # We curry these to avoid reallocating memory each time
    assigs = inst.varAssignment
    watcherst = Vector{AbstractAssignment}(undef, 2)
    literalsholder = Vector{Tuple{inst.signedtp,AbstractAssignment}}(undef, inst.numVars)
    undecidedholder = [1, 2]
    watcherstloop::AbstractAssignment = Undecided
    cflc::Bool = true
    # Checks watched literals of clause
    function internal(cls::Clause{K}) where {K}
        # If watchers are none then clause is unit
        if length(cls.watchers) == 0
            as = checkAssignment(assigs, cls.literals[1])
            if as == Satisfied
                return None()
            elseif as == Conflict
                return Bad()
            elseif as == Undecided
                return Some(cls.literals[1])
            else
                error("not reachable")
            end
        else
            map!(x -> checkAssignment(assigs, cls.literals[x]), watcherst, cls.watchers)
            # If watched lits are satisified return
            if literalInState(watcherst, Satisfied)
                return None()
            # If they are in conflict try to find new ones
            elseif literalInState(watcherst, Conflict)
                lnlit = length(cls.literals)
                map!(x -> (x, checkAssignment(assigs, cls.literals[x])), literalsholder, 1:lnlit)
                literalsSt = view(literalsholder, 1:lnlit)
                setsat = 1
                numUndec = 0
                for i = 1:lnlit
                    lit = literalsSt[i]
                    if setsat == 3 || numUndec == 2
                        break
                    elseif lit[2] == Satisfied
                        cls.watchers[setsat] = lit[1]
                        setsat += 1
                    elseif lit[2] == Undecided
                        numUndec += 1
                        undecidedholder[numUndec] = i

                    end
                end
                # Found new sat literals return 
                if setsat != 1
                    return None()
                else
                    # No undecided literals all are in conflict need to backtrack
                    if numUndec == 0
                        return aBad
                    # Unit Propagation!
                    elseif numUndec == 1
                        return Some(cls.literals[undecidedholder[1]])
                    else
                        # Found new watched literals , clause is not unit
                        cls.watchers[1] = undecidedholder[1]
                        cls.watchers[2] = undecidedholder[2]
                        return None()
                    end
                end
            end
            # watched literals are both undecided nothing to do
            None()
        end
        None()
    end
    return internal
end

# Assign literal and add it to stack
function assignLiteral(inst::SATInstance, lit::Number)
    res = setAssignment(inst, lit)
    if res isa Bad
        return Bad
    end
    # We assigned a literal through unit prop reset counter
    inst.assigCount = 0
    return None
end

# In the beginning we should do a full pass to find unit literals
# Go through all clauses until all units are fully propagated
function propUnitLiteralsFull(inst::SATInstance, watcherfunc::Function, vr)
    cont = true
    while cont
        cont = false
        for cindex = 1:inst.numClauses
            clause = inst.clauses[cindex]
            res = watcherfunc(clause)
            if res isa None
                continue
            elseif res isa Bad
                return Bad()
            elseif res isa Some
                assignLiteral(inst, res.value)
                cont = true
                continue
            else
                error(join("should not be reached res was : ", res))
            end
        end
    end
    return None()
end
# Helper to pretty print a clause for debugging
function printClause(inst::SATInstance, c)
    for lit in inst.clauses[c].literals
        print("(", lit, ", ", inst.varAssignment[(abs(lit))], ") ")
    end
    println("")
end

# Given a SAT Instance , a function to check watched literals and the most recent variable that was branched
# Checks all clauses in which vr occurs to see if unit prop is possible
function propUnitLiterals(inst::SATInstance, watcherfunc::Function, vr::T) where {T<:Integer}
    # Dummy value for first recurrence
    if vr == 0
        return None()
    end
    res::Option = aBad
    for cindex in getVarClauses(inst, vr)
        res = watcherfunc(inst.clauses[cindex])
        # Nothing to Do continue
        if res isa None
            continue
        # Clause is in conflict return 
        elseif res isa Bad
            return Bad()
        # Unit Prop!
        elseif res isa Some
            # Assign unit and recur
            assignLiteral(inst, res.value)
            res = propUnitLiterals(inst, watcherfunc, -res.value)
            # If assignment causes conflict return
            if res isa Bad
                return Bad()
            end
        else
            error(join("should not be reached res was : ", res))
        end
    end
    return None()
end
# Randomly decide sign of variable
function rand_sign()
    if rand(1:2) == 1
        Positive
    else
        Negative
    end
end
#implementation of Jerslow Wang 
# Takes sat instance and array to use to calculate values
function pickJSW(inst::SATInstance,jswraw :: Vector{Tuple{Vector{T},Vector{Float16}}}) where T <: Integer
    # Reset array to 0
    foreach(x -> jswraw[x][2][1] = 0.0,1:inst.numVars)
    clause_len = 0

    for clause in inst.clauses
        clause_len = length(clause.literals)
        is_sat = false
        # Only consider clause if it is not Satisfied
        for literal in clause.literals
            if checkAssignment(inst.varAssignment, literal) == Satisfied
                is_sat = true
                break
            end
        end
        # If not satisified calculate statistics
        if !is_sat
            for literal in clause.literals
                jswraw[abs(literal)][2][1] += (2.0)^(-clause_len)
            end
        end
    end
    # Extract values for sorting - needed due to MASSIVE perfomance difference
    jswpair = [(index[1], val[1]) for (index, val) in jswraw]
    # Use Quicksort (in place) not merge sort (default)
    sort!(jswpair, by = x -> x[2], rev = true,alg=QuickSort)
    #Returns variable with highest JSW score that has not been assigned
    function internal()
        for (lit, val) in jswpair
            if inst.varAssignment[lit] == Unset
                return Some((lit, rand_sign()))
            else
                continue
            end
        end
        # No unassigned variables
        return None()
    end
end

# 1 - Positive -1 : Negative 0 : Undefined 2 : Mixed
# Perform Pure literal elimination
function pureLiteralElimination(inst::SATInstance)
    purelit = Vector{Int8}(undef, inst.numVars)
    fill!(purelit, 0)
    signlit::Int8 = 0
    absLit::inst.usignedtp = 0
    function internal()
        fill!(purelit, 0)
        for clause in inst.clauses
            for literal in clause.literals
                abslit = abs(literal)
                signlit = sign(literal)
                if inst.varAssignment[abslit] != Unset
                    continue
                elseif purelit[abslit] == 0
                    purelit[abslit] = signlit
                elseif purelit[abslit] == 1 && signlit == -1
                    purelit[abslit] = 2
                elseif purelit[abslit] == -1 && signlit == 1
                    purelit[abslit] = 2
                else
                    continue
                end
            end
        end
        for (lit, value) in enumerate(purelit)
            if value == 1
                inst.varAssignment[lit] = Positive
            elseif value == -1
                inst.varAssignment[lit] = Negative
            else
                continue
            end
        end
    end
    return internal
end
# Check if any clause is in conflict
function checkConflict(inst::SATInstance, watcherfunc::Function)
    res::Option = None()
    for clause in inst.clauses
        res = watcherfunc(clause)
        if res isa Bad
            return Bad()
        end
    end
    return None()
end
#Check if ALL clauses are Satisfied
function isSatisified(inst::SATInstance)
    for clause in inst.clauses
        for lit in clause.literals
            if checkAssignment(inst.varAssignment,lit) == Satisfied
                continue
            end
            return false
        end
    end
    return true
end
# Convert Positive , Negative to numbers
function to_sign(l::LiteralState)
    if l == Positive
        return 1
    elseif l == Negative
        return -1
    else
        error("bad")
    end
end

# DPLL implementation
function _dpll(inst::SATInstance)
    # A bunch of variables to curry to avoid recurring on them
    # Function to check watched literalsholder
    watcherfunc = checkWatchers(inst)
    # Array to hold statistics for Jerslow Wang
    jswraw = Vector{Tuple{Vector{inst.signedtp},Vector{Float16}}}(undef, inst.numVars)
    #Initialize array
    foreach(x -> jswraw[x] = ([x],[0.0]),1:inst.numVars)
    # calculate JSW
    pickVar = pickJSW(inst,jswraw)
    # Our pureliteral function
    pureLitfunc = pureLiteralElimination(inst)
    # Unit propgation on entire clause set
    propUnitLiteralsFull(inst, watcherfunc, 0)
    # Eliminate Pure literals 
    pureLitfunc()
    # Recursivelly call dpll , vr is most recent variable branched on
    function dpll(vr::T) where {T<:Integer}
        #BCP
        # Increase counter of guesses
        inst.assigCount += 1
        # If more than 2 guesses since last unit prop
        if inst.assigCount > 2
            # if clause set is satisifed (early!) then return
            if isSatisified(inst)
                return None()
            else
                # Else recalculate JSW and reset counter
                pickVar = pickJSW(inst,jswraw)
                inst.assigCount = 0
            end
        end
        # Create new stack for new decision levels
        newStackCall(inst)
        # Prop unit literals
        res = propUnitLiterals(inst, watcherfunc, -vr)
        #Unit prop led to conflict return
        if res isa Bad
            unwindStack(inst)
            return res
        else
            # Pick new  variable
            VTB = pickVar()
            #No variables left to pick
            if VTB isa None
                return checkConflict(inst, watcherfunc)
            else
                # Try one assignment first
                VTB = VTB.value
                inst.varAssignment[VTB[1]] = Positive
                res = dpll(VTB[1])
                #SAT ! return
                if res isa None
                    return res
                else
                    # Try opposite assignment
                    inst.varAssignment[VTB[1]] = Negative
                    res = dpll(-VTB[1])
                    # UNSAT unwind stack and return
                    if res isa Bad
                        inst.varAssignment[VTB[1]] = Unset
                        unwindStack(inst)
                    end
                    return res
                end
            end
        end
    end
    #Start with dummy value
    return dpll(0)
end

# SAT Solve cnf instance given in file fl
function calc_inst(fl::String)
    # Start timer
    start_time = Base.Libc.time()
    # Read CNF
    inst = read_cnf(fl)
    #DPLL 
    res = _dpll(inst)
    # End
    end_time = Base.Libc.time()
    total_time = end_time - start_time
    # Print output
    if res isa None
        giveOutput(fl, total_time, SAT(inst.varAssignment))
    elseif res isa Bad
        giveOutput(fl, total_time, UNSAT())
    else
        error("why oh why", res)
    end
end
#Pass command line arguments
function __init__()
    __precompile__()
    calc_inst(ARGS[1])
end
end