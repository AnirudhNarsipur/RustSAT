# Marks whether a literal is satisified , in conflict or undecided
@enum AbstractAssignment::Int8 Satisfied Conflict Undecided
# Marks whether Variable is Positive , Negative , Unset  : Notice difference between variable and literal
@enum LiteralState::Int8 Positive Negative Unset

# Option type to convey values back and forth
abstract type Option end
# Return a value
struct Some{T} <: Option
    value::T
end
# None - silent positive
struct None <: Option end
#Bad - failure
struct Bad <: Option end
# DPLL Result
abstract type Satisfiability end
# Variable -> Assignment if SAT
struct SAT{T} <: Satisfiability
    assignment::Dict{T,LiteralState}
end
# Return UNSAT
struct UNSAT <: Satisfiability end

# Dynamic Array implementation
mutable struct DynamicVec{T}
    top::UInt64
    vec::Vector{T}
end

# Holds a the literals of a clause and it's watchers (2 watchers)
#watchers holds indices not literals
# If Clause is unit then watchers are empty
struct Clause{T}
    literals::Vector{T}
    watchers::Vector{T}
end
# Override equality for clauses
Base.:(==)(x::Clause, y::Clause) = x.literals == y.literals && x.watchers == y.watchers
# Stores all data for a SAT instance
# Uses parametric types to reduce memory usage where possible
mutable struct SATInstance{T,K}
    # Unsigned Type for storing variables
    usignedtp::Type
    # Signed type for literals
    signedtp::Type
    # Number of variables
    numVars::T
    # number of clauses
    numClauses::T
    # Variable to Assigment mapping (Hash map)
    varAssignment::Dict{T,LiteralState}
    #Array of clauses
    clauses::Vector{Clause{K}}
    # Stack to keep track of assigments to undo in case of backtracking
    decisionStack::DynamicVec{DynamicVec{T}}
    # Variables to clauses they occur in. Seperate dynamic array for positive and negative occurences
    varClause :: Vector{Pair{DynamicVec{T},DynamicVec{T}}}
    # Counts number of calls since a unit prop
    assigCount :: Int32
end

#Initialize a dynamic array of type tp
function initializeDynamicVec(tp::Type)
    DynamicVec{tp}(0, Vector{tp}(undef, 1))
end
# Push an element to a dynamic array
function pushElem(dvec::DynamicVec{T}, elem::T) where {T}
    ln = length(dvec.vec)
    if dvec.top == ln
        resize!(dvec.vec, ln * 2)
    end 
    dvec.vec[dvec.top+1] = elem
    dvec.top += 1
end
# Pop element from dynamic array
function popElem(dvec::DynamicVec{T}) where {T}
    if dvec.top == 0
        Bad()
    else
        tmp = dvec.vec[dvec.top]
        dvec.top -= 1
        return Some(tmp)
    end
end
# Array slices create a new array which we do not want!
# Instead return a reference to a dynamic array
function viewDvec(dvec :: DynamicVec{T}) where {T}
        return view(dvec.vec,1:dvec.top)
end
# Our actual Stack is a 2D Dynamic array where each element is an array of all decisions made at
# a single level
# Another function to deal with this
function pop2DElem(dvec :: DynamicVec{DynamicVec{T}}) where {T}
    if dvec.top == 0
        return Bad()
    else
        tmp = dvec.vec[dvec.top]
        dvec.top -= 1
        if tmp.top == 0
           return Bad()
        else
            return Some(view(tmp.vec,1:tmp.top))
        end         
    end 
end
# Push an element to 2D Dynamic Array
function push2DElem(dvec :: DynamicVec{DynamicVec{T}},elem :: T) where {T}
    if dvec.top == 0
        pushElem(dvec,initializeDynamicVec(T))
    end
    pushElem(dvec.vec[dvec.top],elem)
    return nothing
end
# Initialize a struct to hold mappings from variables to clauses
function initializeVarClause(numVars :: Number,tp::Type)
    varClause = Vector{Pair{DynamicVec{tp},DynamicVec{tp}}}()
    resize!(varClause,numVars)
    for index=1:numVars
        varClause[index] = Pair(initializeDynamicVec(tp),initializeDynamicVec(tp))
    end
    varClause
end
# Initialize a SAT instance 
function initializeInstance(vars::Number, clauses::Number)
    sattp = getnumtype(clauses, vars)
    clausevec = Vector{Clause{sattp.second}}(undef, clauses)
    resize!(clausevec,clauses)
    SATType = SATInstance{sattp...}
    assigs = map(x -> (abs(x), Unset), 1:vars)
    varClause = initializeVarClause(vars,sattp.first)
    SATType(sattp.first, sattp.second, vars, clauses, Dict(assigs), clausevec,initializeDynamicVec(DynamicVec{sattp.first}),varClause,0)
end
# Given a raw array of literals create a Clause struct
function getClause(literals, tp::Type)
    @assert !(0 in literals)
    ltrslen = length(literals)
    if ltrslen == 0
        return nothing
    elseif ltrslen == 1
        Clause{tp}(literals, [])
    else
        Clause{tp}(literals, [1, 2])
    end
end
# Given num of clauses and vars calculates appropriate num type
# Choose to go with type of max(clauses,var)
function getnumtype(clauses::Number, vars::Number)
    choose = clauses > vars ? clauses : vars
    tps = [Int8, Int16, Int32, Int64, Int128]
    mapping = Dict(
        Int8 => UInt8,
        Int16 => UInt16,
        Int32 => UInt32,
        Int64 => UInt64,
        Int128 => UInt128,
    )
    for tp in tps
        if choose < typemax(tp)
            return Pair(mapping[tp], tp)
        end
    end
    error("Clause set is too large Overflow")
end
# Update varClause index with results from clause at index
function updateVarClause(inst :: SATInstance,index :: Number)
    ablit = 0
    for lit in inst.clauses[index].literals 
        ablit = abs(lit)
        if ablit == lit 
            pushElem(inst.varClause[ablit].first,convert(inst.usignedtp, index))
        else
            pushElem(inst.varClause[ablit].second,convert(inst.usignedtp, index))
        end
    end
end

# Get the clauses in which lit occurs
function getVarClauses(inst :: SATInstance,lit :: T) where T <: Integer
    if sign(lit) == 1
        return viewDvec(inst.varClause[lit].first)
    else
        return viewDvec(inst.varClause[abs(lit)].second)
    end
end