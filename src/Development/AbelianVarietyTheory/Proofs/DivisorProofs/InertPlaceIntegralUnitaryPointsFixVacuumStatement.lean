module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuum
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

theorem _root_.GlobalTheory.T.inertPlace_integralUnitaryPoints_fix_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
    ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
  first | exact @GlobalTheory.InertBridge.fix_vac | exact GlobalTheory.InertBridge.fix_vac | (intros; apply GlobalTheory.InertBridge.fix_vac <;> assumption)
