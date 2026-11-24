module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.MuGal

private theorem cr_square_same_base {O : Type} [CommRing O] {F : B.Fn O} {b : Base}
    {h : b.t = 1} {κm κb : O →+* b.R ⧸ b.I} {Λ : Type} [CommRing Λ] {c : Λ →+* b.R}
    {g : b.R →+* b.R} {τ : Λ →+* Λ}
    (ma : Mor (F.cr b h κm) (F.cr b h κm) g)
    (m : Mor (F.cr b h κm) (F.cr b h κb) (RingHom.id b.R))
    (md : Mor (F.cr b h κb) (F.cr b h κb) g)
    (hg : ∀ a, g (c a) = c (τ a))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F.cr b h κb).Pt.obj B₀),
      (ma.pt.app B₀ (m.pt.app B₀ y)).1.2 = (m.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (t : CH.H (B.OM (F.cr b h κm) c) j) :
    (B.omMor (c := c) (c' := c) md τ hg).pull j
        ((B.omMor (c := c) (c' := c) m (RingHom.id Λ) (fun _ => rfl)).pull j t) =
      (B.omMor (c := c) (c' := c) m (RingHom.id Λ) (fun _ => rfl)).pull j
        ((B.omMor (c := c) (c' := c) ma τ hg).pull j t) :=
  (cr_square ma m m md hg (fun _ => rfl) (fun _ => rfl) hg (fun _ => rfl) hpt j t).symm

theorem mu_gal {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j) :
    B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) = Mid.mu r M n j hT (galM r M σ hσ n j t) := by
  let F := B.schFn M.p
  let b := B.bs l true n
  let κm := Mid.κm r n
  let κb := B.κb (okToOC l K) true n
  let g := galBase σ n
  let c := (base l).cris n
  let ma := B.crMor (F := F) (F' := F) (b := b) (b' := b) (ht := rfl) (ht' := rfl)
    (κ := κm) (κ' := κm) g rfl (B.dd_gal true σ n)
    (B.basePt F _ (gal_κm r σ hσ n)) fun _ _ _ => rfl
  let md := B.crMor (F := F) (F' := F) (b := b) (b' := b) (ht := rfl) (ht' := rfl)
    (κ := κb) (κ' := κb) g rfl (B.dd_gal true σ n)
    (B.basePt F _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl
  refine cr_square_same_base (O := OK l K) (F := F) (b := b) (h := rfl) (κm := κm) (κb := κb)
    (Λ := Acris l) (c := c) (g := g) (τ := ACris.galCris σ)
    ma (Mid.mIn r M n hT) md (galBase_cris σ n) ?_ j t
  intro B₀ y
  -- Give the kernel the common point explicitly, before either composite is unfolded.
  exact Eq.refl (F.Pt.map (CommRingCat.ofHom (Mid.frbN (Mid.l_zero y.1.1) N)) y.1.2)

end GlobalTheory.CompanionTheory.MuGal
