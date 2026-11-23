module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHermitianFormInertPointEqLocalForm
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.tensorHermitianForm_inertPoint_eq_localForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  first | exact @GlobalTheory.InertTens.hTens_kap_eq_locH | exact GlobalTheory.InertTens.hTens_kap_eq_locH | (intros; apply GlobalTheory.InertTens.hTens_kap_eq_locH <;> assumption)
