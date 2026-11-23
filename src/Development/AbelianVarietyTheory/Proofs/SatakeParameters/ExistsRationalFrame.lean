module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LatticeFramesPrimeToLevel
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.UnUnitCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

section Units

variable {l : ℕ} [Fact l.Prime] {lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]}

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem emb_mem {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) : φ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))

end Units


variable {D : D7} {Dx : DivX D} {Tw : TwForms D}



variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {C : CharFrame D} {nch : NChoice D}

variable (E : KerEnt D Dx Tw) (Tp : TupTied D C nch) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ)


end GlobalTheory.UnUnitCmp
