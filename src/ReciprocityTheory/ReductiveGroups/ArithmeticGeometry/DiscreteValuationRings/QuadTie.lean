module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Nat.Cast.Order.Ring

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.DVR

variable {𝕜 W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup W] [Module 𝕜 W]

def qf (B : LinearMap.BilinForm 𝕜 W) (w : W) : 𝕜 := B w w / 2

variable {B : LinearMap.BilinForm 𝕜 W}

end ReciprocityTheory.ChartRestriction.G.DVR
