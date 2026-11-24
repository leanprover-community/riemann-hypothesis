module

public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.SuppOffPlace

section Gen

variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

theorem prV_entry_eq_zero {n : ℕ} (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (w : HeightOneSpectrum (𝓞 F))
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) w) g = 1) (i j : Fin n) : Formalism.UG.prV (E := E) w ((g.val - 1) i j) = 0 := by
  have h1 : (Formalism.UG.bc (Formalism.UG.prV (E := E) w) g).val i j = (1 : GL (Fin n) (E ⊗[F] w.adicCompletion F)).val i j := by
    rw [h]
  rw [Formalism.UG.bc, Units.coe_map] at h1
  change Formalism.UG.prV (E := E) w (g.val i j) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] w.adicCompletion F)) i j at h1
  rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eps_mul_of_off (v : HeightOneSpectrum (𝓞 F)) {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hy : ∀ w, w ≠ v → Formalism.UG.prV (E := E) w y = 0) : Formalism.UG.P.afsplitEps E v * y = y := by
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub, map_mul]
  by_cases h : w = v
  · subst h
    rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
  · rw [hy w h, mul_zero, sub_zero]

end Gen

variable {D : D7}

theorem belowPl_conjP {v : HeightOneSpectrum (𝓞 D.host.F)} {Pb : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.L2.Col.IsOver v Pb) : Formalism.IndefR.Fin.belowPl (D := D) (Formalism.L2.Col.conjPrime₂ Pb) = v := by
  apply HeightOneSpectrum.ext
  rw [h]
  ext x
  show Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ∈ Pb.asIdeal ↔
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ Pb.asIdeal
  have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
    rw [show ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) from rfl]
    exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  rw [this]

theorem afsplitI_one (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Formalism.UG.P.afsplitI v (1 : v.adicCompletion D.host.F) = Formalism.IndefR.Fin.sglV v 1 := by
  apply Formalism.IndefR.Fin.af_ext
  intro w
  by_cases hw : w = v
  · subst hw
    rw [Formalism.IndefR.Fin.sglV_same]
    exact Formalism.UG.P.afsplitI_self w 1
  · rw [Formalism.IndefR.Fin.sglV_ne v _ hw]
    exact Formalism.UG.P.afsplitI_ne v w hw 1

theorem swap_finPart_phiE (v : HeightOneSpectrum (𝓞 D.host.F)) :
    swapAE D (finPart D (Formalism.IndefR.Fin.phiE v 1)) = Formalism.UG.P.afsplitEps D.host.E v := by
  rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul, afsplitI_one]
  rfl

theorem suppAt_of_trivial_off : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ α : GA D V, α ∈ GfC V → (∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1) → SuppAt e V α := by
  intro D V v Pb e hO hI α hα hw
  rw [GlobalTheory.HeckeTrans.suppAt_iff e hα, Formalism.IndefR.Fin.below_of_idemAt hI, belowPl_conjP hO,
    ← GlobalTheory.HeckeTrans.finE_unswap]
  have hM : (finE V α).val.map
      (GlobalTheory.HeckeTrans.unswap D) - 1 =
      ((finE V α).val - 1).map
      (GlobalTheory.HeckeTrans.unswap D) := by
    rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  rw [hM]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  apply Function.LeftInverse.injective (GlobalTheory.HeckeTrans.unswap_swap (D := D))
  rw [map_mul, swap_finPart_phiE, GlobalTheory.HeckeTrans.swap_unswap]
  exact eps_mul_of_off v (fun w hw' => prV_entry_eq_zero _ w (hw w hw') i j)

end GlobalTheory.Mem.SuppOffPlace
