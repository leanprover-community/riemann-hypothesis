module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegularStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModelStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelRightStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatiosStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGeneratorsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

def segIxEquiv : ((k : K₀ ⊕ StepIx Ψ p q) → idx (p := p) (q := q) J₀ n k) ≃
    FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q) :=
  Equiv.sumPiEquivProdPi (idx (p := p) (q := q) J₀ n)

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF
  classical
  obtain ⟨hL, hc, hφ, hB⟩ := hF
  set r := rk (CMType H) D.p D.q with hr
  set x : ((k : K₀) → J₀ k) → Ω := seg x₀ with hxdef
  set cF := cc 𝔐 bW bO with hcF
  have hx : CoordTie ℤ 𝔐.ξ x := 𝔐.tie
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt 𝔐.ξ, specializes_refl _⟩
  have hB' : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (cF s l)) = 1 := hB
  obtain ⟨J₁, hJ₁, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω (EE 𝔐) (CMType H ⊕ CMType H) r n ((k : K₀) → J₀ k) x φ cF c₀ hc₀.1
    (GlobalTheory.T.function_field_ratio_generators 𝔐.X Ω 𝔐.ξ _ x c₀ hx hc₀.1) hB'
  have : Finite (FlagIx ((k : K₀) → J₀ k) n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    GlobalTheory.T.exists_proper_integral_model (GenField Ω r) ℤ (FlagIx ((k : K₀) → J₀ k) n r) (flagCoord _ x φ cF) J₁ hJ₁ hfrac
  obtain ⟨f, hdom, hch⟩ := GlobalTheory.T.dominates_of_coords_regular 𝔐.X Ω 𝔐.ξ ℤ _ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simp [intCast_mem (regAt ξ' p') z]) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord _ x φ cF (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsm := GlobalTheory.T.flag_frames_generic_model_right 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ x (CMType H ⊕ CMType H) r (VV 𝔐) (LL 𝔐) m n φ cF X' ξ' f hx 𝔐.all hL hφ hc
    hx' hirr' hdom hch
  have hseg : seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) =
      flagCoord ((k : K₀) → J₀ k) x φ cF ∘ segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀) := by
    funext c'
    show ∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, c' k⟩ =
      algebraMap Ω (GenField Ω r) (∏ k, x₀ ⟨k, c' (.inl k)⟩) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (c' (.inr q)) (Fin.castLE q.2.2)).det
    rw [Fintype.prod_sum_type, map_prod]
    rfl
  refine ⟨X', ξ', f, ?_, hirr', hdom, hsm⟩
  rw [hseg]
  convert coordTie_comp_equiv hx' (segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀)) using 1 <;> exact Subsingleton.elim _ _
