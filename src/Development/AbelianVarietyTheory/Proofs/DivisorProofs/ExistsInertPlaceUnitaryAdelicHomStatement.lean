module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceUnitaryAdelicHom
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_inertPlace_unitary_adelicHom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {n : ℕ} (X : Spc F E n) (P : GL (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) *
        (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = δ • 1 →
      ∀ {Γ : Type} [Group Γ] (φ : Γ →* GL (Fin n) (w.adicCompletion E)),
        (∀ g, (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = 1) →
        ∃ ι : Γ →* UA σ X.J, (∀ g, ι g ∈ UAt σ X (evFin F v)) ∧
          (∀ g, (mat (ι g)).map (locW h) = ((P * φ g * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
          (IsFrameAt w X.L P → ∀ g, φ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (w.adicCompletion E)) → ι g ∈ GlobalTheory.InertSph.KAt σ X v) := by
  first | exact @GlobalTheory.InertPlace.exists_hom_inert | exact GlobalTheory.InertPlace.exists_hom_inert | (intros; apply GlobalTheory.InertPlace.exists_hom_inert <;> assumption)
