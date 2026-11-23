module

public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open NumberField Polynomial Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.FamSep

section General

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {m : ℕ} (A : FamIn K G Pl0 T m)

theorem trScale_ne_zero_at {P : Pl0} (hq : A.q P ≠ 0) : trScale A.r m A.t A.q A.etaVal P ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))

theorem typesSep_of_local (hq : ∀ P : (A.fam.R A.fam.μ0).Pl, A.q ((A.fam.R A.fam.μ0).pl P) ≠ 0)
    (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep := by
  intro Sg hSg Sg' hSg' hne j
  obtain ⟨P, hP⟩ := (A.fam.R A.fam.μ0).sep_of_mem_ixFin hSg hSg' hne
  exact ⟨P, fun h => hP (dualPoly_inj (trScale_ne_zero_at A (hq P)) (A.const_of h0 Sg hSg _) (A.const_of h0 Sg' hSg' _) h)⟩

theorem typesSep_of_ok {s : ℕ} (hOk : A.fam.Ok s) (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep :=
  typesSep_of_local A (fun P => ((hOk.what₂ A.fam.μ0).q_pos P).ne') h0

end General

section Real

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Real

end GlobalTheory.FamSep

end
