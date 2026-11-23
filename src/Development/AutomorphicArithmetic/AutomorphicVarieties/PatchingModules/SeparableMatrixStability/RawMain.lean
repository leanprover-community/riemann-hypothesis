module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AutDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.NonssDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PairDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PtDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ResidDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TwquotEx
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.raw_main :
    CoreBC → Raw := by
  intro core l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D A hl hA hgen h x hcard
  obtain ⟨Q⟩ := twquot_ex l L G0 T
  have hopen : IsOpen (T.H.toSubgroup : Set G0.Γ) := T.H.toOpenSubgroup.isOpen
  have hle : T.H.toSubgroup ≤ G0.η.ker := fun a ha => T.H_η a ha
  have hPL : PL l T.H.toSubgroup ≤ T.H.toSubgroup := (pl_props l G0.Γ T.H.toSubgroup hopen).2.2.1
  obtain ⟨r', hc, hIp⟩ := resid_desc l L G0 Q.G0' Q.g0 n O r (fun a ha i => hA.1 a (hPL (by
    rw [← Q.ker0, MonoidHom.mem_ker, ← Glob.Hom.coe_p₀, ha]; rfl)) i)
  obtain ⟨u', hD, hψ⟩ := pair_desc l L G0 Q.G0' Q.g0 n O r r' B u T.H.toSubgroup hopen hle hA.1 Q.ker0 hc
  obtain ⟨A'⟩ := aut_desc l L G0 T Q n O r r' B u u' J Empty D hA hc hD hψ A
  choose x' hker hK using fun i => pt_desc l L G0 T Q n O r r' B u u' (D + n * T.q) (x i) hA hc hD hψ
  have hns := nonss_desc l L G0 Q.G0' Q.g0 n O r r' B u u' T.H.toSubgroup hopen hle hA.1 Q.ker0 hc hD hψ
  have hA' : Adapted Q.grp (r := r') := by
    refine ⟨fun g hg i => ?_, hIp hA.2⟩
    obtain ⟨a, rfl⟩ := Q.g0.p₀_surj g
    have := hA.1 a ((Q.H'_iff a).1 hg) i
    rw [hc.1 i] at this
    exact this
  have hsub : pairVals u ⊆ pairVals u' := by
    rintro b (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
    · refine Or.inl ⟨i, Q.g0.p₀ g, ?_⟩
      rw [← hD, (comap_lam n B _ _ Q.g0.p₀ u'.D).2.1]
      congr 1
      exact MonoidAlgebra.mapDomain_single
    · exact Or.inr ⟨v, i, g, by rw [hψ]⟩
  have hgen' : GenBy O (pairVals u') := fun N b =>
    (hgen N b).imp fun a ha => ⟨Algebra.adjoin_mono hsub ha.1, ha.2⟩
  have main := core l L Q.G0' Q.grp n O r' B u' J D A' hl Q.proL hA' hgen' h x'
    (fun i => by rw [hK i, hK 0]; exact hcard i)
  have hfun : (fun i => RingHom.ker (x' i).f) = fun i => RingHom.ker (x i).f := funext hker
  rw [hfun] at main
  intro e he hq q hqp hqle hst
  refine main e (fun i => ⟨(he i).1, (hns _).1 (he i).2.1, (he i).2.2⟩) ?_ q hqp hqle ?_
  · obtain ⟨q₁, h1, h2, h3⟩ := hq
    exact ⟨q₁, h1, (hns _).2.1 h2, h3⟩
  · exact hst.imp (hns q).2.1 (hns q).1
