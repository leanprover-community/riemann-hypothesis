module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

namespace GlobalTheory.LocLanglands

section Transport

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fixed_ne_bot_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (hπ : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hπ
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => h0 ?_⟩
  · exact (φ.toIntertwiningMap.isIntertwining _ _ u v).symm.trans
      (congrArg φ (GlobalTheory.Parabolic.mem_fixed.1 hv u hu))
  · exact φ.toLinearEquiv.injective (h1.trans (map_zero _).symm)

end Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def toIrrRep {n : ℕ} (π : Irr (w.adicCompletion E) n) : IrrRep (GL (Fin n) (w.adicCompletion E)) :=
  ⟨π.V, π.π, π.smooth, π.irr⟩

end GlobalTheory.LocLanglands
