module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSymplecticFormFrameCoordinatesEqLocalTrace
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.weil_symplectic_form_frame_coordinates_eq_local_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) →
      ∀ (PV JS : GL (Fin n) L) (PW JT : GL (Fin d) L),
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι PV X.J →
        (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι PW W.J)ᵀ →
        ∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) := by
  first | exact @GlobalTheory.InertLocSymp.psi_symp_eq | exact GlobalTheory.InertLocSymp.psi_symp_eq | (intros; apply GlobalTheory.InertLocSymp.psi_symp_eq <;> assumption)
