using Test
include("./solver.jl")
include("./pbt.jl")
@testset "read_cnf_test" begin
    read_cnf("small_inst/toy_solveable.cnf")
    read_cnf("input/C168_128.cnf")
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
    @test checkWatchers(assigs1,cls1) == Some{Int8}(1)
    assigs = Dict([(1,Unset),(2,Negative),(3,Positive),(4,Positive),(5,Unset),(6,Unset)])
    cls = getClause([1,-2],Int8)
    @test checkWatchers(assigs,cls) isa None
    cls2 = getClause([1,2,4],Int8)
    @test cls2.watchers == [1,2]
    @test checkWatchers(assigs,cls2) isa None
    @test issubset(Set(Int8[3]),Set(cls2.watchers))   #indices
    cls3 = getClause([2,-3,4],Int8)
    @test checkWatchers(assigs,cls3) isa None
    @test issubset(Set(Int8[3]),Set(cls3.watchers))
    cls4 = getClause([2,-3,-4],Int8)
    @test checkWatchers(assigs,cls4) isa Bad
    cls5 = getClause([2,-3,5],Int8)
    @test checkWatchers(assigs,cls5) == Some{Int8}(5)
    cls6 = getClause([2,-3,-5],Int8)
    @test checkWatchers(assigs,cls6) == Some{Int8}(-5)
    cls7 = getClause([2,-3,-5,6],Int8)
    @test checkWatchers(assigs,cls7) isa None
    cls8 = getClause([1,5,6],Int8)
    @test checkWatchers(assigs,cls8) isa None
    @test issubset(Set(Int8[1,2]),Set(cls8.watchers))
end
@testset "propUnitLiterals" begin
    inst =  read_cnf("test_inst/test0.cnf")
    propUnitLiterals(inst)
    @test true
    inst = read_cnf("test_inst/test1.cnf")
    propUnitLiterals(inst)
    @test inst.varAssignment[1] == Unset && inst.varAssignment[2] == Unset && inst.varAssignment[3] == Unset
    inst = read_cnf("test_inst/test2.cnf")
    propUnitLiterals(inst)
    @test inst.varAssignment == Dict([(1,Positive),(2,Unset),(3,Negative),(4,Positive)])
    inst = read_cnf("test_inst/test3.cnf")
    res = propUnitLiterals(inst)
    @test res == Bad()

end

# @testset "setAssignment" begin
#     inst = initializeInstance(6,4)
#     inst.varAssignment = Dict([(1,Unset),(2,Negative),(3,Positive),(4,Positive),(5,Unset),(6,Unset)])
#     assigs = inst.varAssignment
#     @test setAssignment(inst,-1) isa None
#     @test assigs[1] == Negative
#     @test setAssignment(inst,2) isa Bad
#     @test setAssignment(inst,3) isa None
#     @test setAssignment(inst,5) isa None
#     @test assigs[5] == Positive
# end
@testset "SAT Itself" begin
    # @test check_inst("input/C168_128.cnf")
    @test check_inst("small_inst/toy_solveable.cnf")
end

@testset "DynamicVec" begin
    st = initializeDynamicVec(Int64)
    @test length(st.vec) == 1
    @test st.top == 0
    pushElem(st,1)
    @test st.top == 1
    @test st.vec == [1]
    pushElem(st,3)
    @test st.top == 2
    @test length(st.vec) == 2
    @test st.vec[1:2] == [1,3]
    pushElem(st,5)
    @test st.top == 3
    @test length(st.vec) == 4
    @test st.vec[1:3] == [1,3,5]
    p1 = popElem(st)
    @test p1  == Some(5)
    @test st.top == 2
    @test length(st.vec) == 4
    @test st.vec[1:3] == [1,3,5]
    pushElem(st,7)
    @test st.vec[1:3] == [1,3,7]
    st2 = initializeDynamicVec(Int64)
    @test popElem(st2) isa Bad
    pushElem(st2,1)
    @test popElem(st2) == Some(1)
    @test popElem(st2) isa Bad

end
# assigs = Dict([(1,Unset),(2,Negative),(3,Positive),(4,Positive)])
# cls3 = getClause([2,-3,4],Int8)
# checkWatchers(assigs,cls3) == 4
# @test checkWatchers(assigs,cls) == Satisfied
