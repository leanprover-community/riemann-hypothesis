module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtLeafSt
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussGenericHeight.GaussGenericStatements.GaussGenericLemmas.TranslationDomainMaps.TranslSEquivApply
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussGenericHeight.GaussGenericStatements.GaussGenericLemmas.TranslationDomainMaps.MapDomainMemOfDvd

@[expose] public section

open NumberField

open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.GaussGen BlockPoly in
theorem HtGaussGen {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type}
    [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type}
    [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A)
    (hx1 : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.PlaceTrivialOrPositive 𝒜 d)
    (hx2 : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.AdmissibleValuationPrimeUnique 𝒜 d) :
    ReciprocityTheory.ChartRestriction.G.T0.LeafSt.GeneratorMultiHomogeneous 𝒜 d := by
  unfold ReciprocityTheory.ChartRestriction.G.T0.LeafSt.GeneratorMultiHomogeneous
  intro hd h c p hp hgood
  obtain ⟨w, hw⟩ := hgood
  by_cases hpp : p.IsPrincipal
  swap
  · have h0 : d.gen p = 0 := by
      unfold ReciprocityTheory.ChartRestriction.G.T0.Data.gen
      rw [dite_eq_right hpp]
    rw [h0]
    unfold ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
    intro s hs
    simp at hs
  have hgen : d.gen p = Submodule.IsPrincipal.generator p := by
    unfold ReciprocityTheory.ChartRestriction.G.T0.Data.gen
    rw [dite_eq_left hpp]

  have key : ∀ σ : KTp K d.D d.N ≃ₐ[K] KTp K d.D d.N, p.comap σ = p →
      Submodule.IsPrincipal.generator p ∣ σ (Submodule.IsPrincipal.generator p) := by
    intro σ hσ
    have h1 : Submodule.IsPrincipal.generator p ∈ p.comap σ := by
      rw [hσ]
      exact Submodule.IsPrincipal.generator_mem p
    obtain ⟨r, hr⟩ :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator p).mp (Ideal.mem_comap.mp h1)
    exact ⟨r, by rw [hr, smul_eq_mul, mul_comm]⟩
  have h2K : (2 : K) ≠ 0 := two_ne_zero
  have h2 : (2 : Ω c) ≠ 0 := by
    intro h0
    apply h2K
    apply (algebraMap K (Ω c)).injective
    rw [map_ofNat, map_zero]
    exact h0

  have hsc : ∀ b, Submodule.IsPrincipal.generator p ∣
      BlockPoly.diag (BlockPoly.cb b (2 : K)) (Submodule.IsPrincipal.generator p) := by
    intro b
    exact key (BlockPoly.diagEquiv (BlockPoly.cb_ne_zero h2K b))
      (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq 𝒜 d hx1 hx2 hd h c p hp w hw _
        (BlockPoly.diagEquiv (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.cS_ne_zero h2 b))
        (fun t => ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_scale (d.jc c) (d.x c) b t))
  have hsw : ∀ e : Equiv.Perm (Fin (d.D + 1)), e 0 = 0 → Submodule.IsPrincipal.generator p ∣
      MvPolynomial.rename (BlockPoly.eT e) (Submodule.IsPrincipal.generator p) := by
    intro e he
    exact key (MvPolynomial.renameEquiv K (BlockPoly.eT e))
      (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq 𝒜 d hx1 hx2 hd h c p hp w hw _
        (MvPolynomial.renameEquiv (Ω c) (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.eS e))
        (fun t => ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_swap (d.jc c) (d.x c) e he t))
  have htr : ∀ a : Fin (d.N + 1) → K, Submodule.IsPrincipal.generator p ∣
      BlockPoly.transl a (Submodule.IsPrincipal.generator p) := by
    intro a
    exact key (BlockPoly.translEquiv a)
      (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq 𝒜 d hx1 hx2 hd h c p hp w hw _
        (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv (d.jc c) (fun j => algebraMap K (Ω c) (a j)))
        (fun t => ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_transl (d.jc c) (d.x c) a t))
  rw [hgen]
  unfold ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
  intro s hs b
  exact BlockPoly.multiHom_of_dvd hsc hsw htr s hs b
