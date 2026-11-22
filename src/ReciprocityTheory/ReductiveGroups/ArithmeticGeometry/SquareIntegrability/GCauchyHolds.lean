module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExtProof
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ImportsAlt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.InvBuild
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchy
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

theorem gSup_holds : GSupStatement := gSup Ext.all.1

theorem dim_holds : DimStatement := dim

theorem split_holds : SplitStatement := split Ext.all

theorem T_holds : TStatement := tOf Ext.all split_holds gSup_holds dim_holds

end ReciprocityTheory.ChartRestriction.G.I2
