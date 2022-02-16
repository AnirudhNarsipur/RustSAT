include("./dimacparser.jl")
#Checks the watchers of the clause and 
# returns literal if it exists
#guarenteed not to have empty clauses

function literalInState(ls::Vector{AbstractAssignment}, st::AbstractAssignment)
    for elem in ls
        if elem == st
            return true

        end
    end
    return false
end

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
function updateStack(inst::SATInstance, literal::Number)
    # println("pushing ",literal," at level ",length(inst.decisionStack))
    # @assert 1 <= convert(inst.usignedtp, abs(literal)) <= inst.numVars
    inst.varAssignment[abs(literal)] = (literal > 0) ? Positive : Negative
    push2DElem(inst.decisionStack, convert(inst.usignedtp, abs(literal)))
    return nothing
end
function newStackCall(inst::SATInstance)
    pushElem(inst.decisionStack, initializeDynamicVec(inst.usignedtp))
end
function unwindStack(inst::SATInstance)
    last = pop2DElem(inst.decisionStack)
    if last isa Bad
        return nothing
    elseif last isa Some
        # println("last is  ",last.value.vec)
        for i in last.value
            # println("i is ",i)
            # @assert 1 <= i <= inst.numVars
            inst.varAssignment[i] = Unset
        end
        return nothing
    else
        error("unreachable!")
    end
end

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
# Returns Option
function checkWatchers(inst::SATInstance) where {T}
    assigs = inst.varAssignment
    watcherst = Vector{AbstractAssignment}(undef, 2)
    literalsholder = Vector{Tuple{inst.signedtp,AbstractAssignment}}(undef, inst.numVars)
    undecidedholder = [1,2]

    function internal(cls::Clause{K}) where {K}
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
            # @assert (length(cls.watchers) == 2)
            map!(x -> checkAssignment(assigs, cls.literals[x]), watcherst, cls.watchers)
            if literalInState(watcherst, Satisfied)
                return None()
            elseif literalInState(watcherst, Conflict)
                lnlit = length(cls.literals)
                map!(x -> (x, checkAssignment(assigs, cls.literals[x])), literalsholder, 1:lnlit)
                # literalsSt = map(x -> (x, checkAssignment(assigs, cls.literals[x])), 1:length(cls.literals))
                #TODO multi filter
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
                        numUndec+=1
                        undecidedholder[numUndec] = i
                        
                    end
                end
                if setsat != 1
                    return None()
                else
                    # undeclit = filter(x -> x[2] == Undecided, literalsSt)
                    if numUndec == 0
                        return Bad()
                    elseif numUndec == 1
                        return Some(cls.literals[undecidedholder[1]])
                    else
                        # @assert numUndec >= 2
                        # @assert 1 <= undecidedholder[1] <= lnlit
                        # @assert 1 <= undecidedholder[2] <= lnlit
                        # @assert undecidedholder[1] == undeclit[1][1]
                        # @assert undecidedholder[2] == undeclit[2][1]

                        cls.watchers[1] = undecidedholder[1]
                        cls.watchers[2] = undecidedholder[2]
                        return None()
                    end
                end
            end
            None()
        end
        None()
    end
    return internal
end

function assignLiteral(inst::SATInstance, literals::Number)
    for lit in literals
        res = setAssignment(inst, lit)
        if res isa Bad
            return Bad
        end
    end
    return None
end

function propUnitLiterals(inst::SATInstance, watcherfunc::Function)
    cont = true
    while cont
        cont = false
        for clause in inst.clauses
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


function verify_inst(inst::SATInstance)
    @assert length(keys(inst.varAssignment)) == inst.numVars
    for i = 1:inst.numVars
        @assert inst.varAssignment[i] == Unset
    end
    for key in keys(inst.varAssignment)
        @assert 1 <= key <= inst.numVars
    end
end

#Dumb Just assings everything to Positive
function pickFirstVar(inst::SATInstance)
    function internal()
        for clause in inst.clauses
            for literal in clause.literals
                if checkAssignment(inst.varAssignment, literal) == Undecided
                    return Some((abs(literal), (literal > 0) ? Positive : Negative))
                end
            end
        end
        return None()
    end
    return internal
end
function pickJSW(inst::SATInstance)
    jswraw = Vector{Float16}(undef, inst.numVars)
    fill!(jswraw, 0.0)
    clause_len = 0
    t = 0
    for clause in inst.clauses
        clause_len = length(clause.literals)
        for literal in clause.literals
            jswraw[abs(literal)] += (2.0)^(-clause_len)
        end
    end
    jswpair = [(index, val) for (index, val) in enumerate(jswraw)]
    sort!(jswpair, by = x -> x[2], rev = true)
    nv = inst.numVars
    function internal()
        for (lit, val) in jswpair
            if inst.varAssignment[lit] == Unset
                return Some((lit, Positive))
            else
                continue
            end
        end
        return None()
    end
end

function opposite(x::LiteralState)
    if x == Positive
        Negative
    elseif x == Negative
        Positive
    else
        error("bad")
    end
end

function _dpll(inst::SATInstance)
    # verify_inst(inst)
    watcherfunc = checkWatchers(inst)
    pickVar = pickJSW(inst)
    function dpll()
        #BCP
        # println("dpll level ",i)
        newStackCall(inst)
        # @assert(length(inst.decisionStack) == i)
        res = propUnitLiterals(inst, watcherfunc)
        if res isa Bad
            unwindStack(inst)
            return res
        else
            # @assert(length(inst.decisionStack) == i)
            VTB = pickVar()
            if VTB isa None
                return None()
            else
                # @assert(length(inst.decisionStack) == i)
                VTB = VTB.value
                # println("VTB is ",VTB)
                @assert 1 <= VTB[1] <= inst.numVars
                inst.varAssignment[VTB[1]] = VTB[2]
                res = dpll()
                if res isa None
                    return res
                else
                    # @assert(length(inst.decisionStack) == i)
                    inst.varAssignment[VTB[1]] = opposite(VTB[2])
                    # compDict(inst.varAssignment,assig,i)
                    res = dpll()
                    if res isa Bad
                        inst.varAssignment[VTB[1]] = Unset
                        unwindStack(inst)
                    end
                    return res
                end
            end
        end
    end
    # verify_inst(inst)
    return dpll()
end

function calc_inst(fl::String)
    inst = read_cnf(fl)
    res = _dpll(inst)
    if res isa None
        giveOutput(fl, 1, SAT(inst.varAssignment))
    elseif res isa Bad
        giveOutput(fl, 1.23, UNSAT())
    else
        error("why oh why", res)
    end
end
# @time calc_inst("small_inst/toy_solveable.cnf")
# @time calc_inst("small_inst/large.cnf")

# @time calc_inst("test_inst/test3.cnf")
# inst = read_cnf("small_inst/toy_solveable.cnf")
# _dpll(inst)
# dc = keys(inst.varAssignment)
# @time check_inst("small_inst/toy_solveable.cnf")
# @time calc_inst("input/C140.cnf")