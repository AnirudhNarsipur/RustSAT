using Test
include("./solver.jl")
@testset "read_cnf_test" begin
    read_cnf("small_inst/toy_solveable.cnf")
    read_cnf("large_inst/C168_128.cnf")
    @test true
end
@testset "check Assignment" begin
    assigs = Dict([(1,Unset),(2,Positive),(6,Negative)])
    @test checkAssignment(assigs,1) == Undecided
    @test checkAssignment(assigs,-1) == Undecided
    @test checkAssignment(assigs,2) == Satisfied
    @test checkAssignment(assigs,-2) == Conflict
    @test checkAssignment(assigs,6) ==  Conflict
    @test checkAssignment(assigs,-6) ==  Satisfied
end
@testset "CreateClause" begin
    @test getClause([1],Int8) == Clause{Int8}([1],[])
    @test getClause([-1,2],Int8) == Clause{Int8}([-1,2],[1,2])
    @test getClause([-1,2,-4,3],Int8) == Clause{Int8}([-1,2,-4,3],[1,2])

end

@testset "checkWatcher" begin
    assigs1 = Dict([(1,Unset)])
    cls1 = getClause([1],Int8)
    @test checkWatchers(assigs1,cls1) == 1
    assigs = Dict([(1,Unset),(2,Negative),(3,Positive),(4,Positive),(5,Unset),(6,Unset)])
    cls = getClause([1,-2],Int8)
    @test checkWatchers(assigs,cls) == Satisfied
    cls2 = getClause([1,2,4],Int8)
    @test cls2.watchers == [1,2]
    @test checkWatchers(assigs,cls2) == Satisfied
    @test issubset(Set(Int8[3]),Set(cls2.watchers))   #indices
    cls3 = getClause([2,-3,4],Int8)
    @test checkWatchers(assigs,cls3) == Satisfied
    @test issubset(Set(Int8[3]),Set(cls3.watchers))
    cls4 = getClause([2,-3,-4],Int8)
    @test checkWatchers(assigs,cls4) == Conflict
    cls5 = getClause([2,-3,5],Int8)
    @test checkWatchers(assigs,cls5) == 5
    cls6 = getClause([2,-3,-5],Int8)
    @test checkWatchers(assigs,cls6) == -5
    cls7 = getClause([2,-3,-5,6],Int8)
    @test checkWatchers(assigs,cls7) == Satisfied
end

# assigs = Dict([(1,Unset),(2,Negative),(3,Positive),(4,Positive)])
# cls3 = getClause([2,-3,4],Int8)
# checkWatchers(assigs,cls3) == 4
# @test checkWatchers(assigs,cls) == Satisfied
