module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DetIntUnit

theorem det_mem_subring {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

theorem det_finM (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) :
    (finM V hn g).det = toEAf D (Formalism.L2.Theta.mt V g).det := by
  unfold finM
  rw [Matrix.det_reindex_self, RingHom.map_det]
  rfl

theorem det_int_unit : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)),
    finM V hn g = k.1 → (∀ i j, k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, (k⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det →
      finPart D (d : Formalism.L2.Theta.AE D) ∈ intAE D ∧ finPart D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := by
  intro D V n hn g k hk h1 h2 d hd
  have e1 : toEAf D (d : Formalism.L2.Theta.AE D) = k.1.det := by
    rw [hd, ← det_finM D V n hn g, hk]
  have i1 : toEAf D (d : Formalism.L2.Theta.AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [e1]; exact det_mem_subring _ _ h1
  have hkk : k.1.det * (k⁻¹).1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdd : toEAf D (d : Formalism.L2.Theta.AE D) * toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have e2 : toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = (k⁻¹).1.det := by
    rw [e1] at hdd
    calc toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)
        = ((k⁻¹).1.det * k.1.det) * toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) := by
          rw [mul_comm (k⁻¹).1.det, hkk, one_mul]
      _ = (k⁻¹).1.det := by rw [mul_assoc, hdd, mul_one]
  have i2 : toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [e2]; exact det_mem_subring _ _ h2
  exact ⟨GlobalTheory.PlaceVec.finPart_mem_intAE i1, GlobalTheory.PlaceVec.finPart_mem_intAE i2⟩

end GlobalTheory.DetIntUnit
