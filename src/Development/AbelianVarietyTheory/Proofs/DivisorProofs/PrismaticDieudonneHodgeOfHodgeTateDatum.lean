module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSeparatesDualLieGhostComponentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupLatticeFreeRankHeightStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MemSmulOfTmulEqZero
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SemilinearFactorsThroughReduction
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat



theorem prismaticDieudonneHodgeAt_of_hasDatum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, HasDatum hε G) → GlobalTheory.Published.PrismaticDieudonneHodgeAt ε := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hD
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by
    simpa only [zeta, Function.iterate_one, pow_one] using hε 1
  obtain ⟨hdom, -, hker, hθ, -, -, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  have hθξ : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _

  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.exists_frobenius_hodgeTateLattice_ainf p C v O hv ε hε

  have hLie := fun G : PDivGroup p O =>
    GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent p C v O hv ε hε G (hD G)
  have hsep : ∀ (G : PDivGroup p O) (x x' : G.dual.Lie),
      (∀ t, x (hodgeTate G t) = x' (hodgeTate G t)) → x = x' := fun G x x' h =>
    sub_eq_zero.1 ((hLie G).1 (x - x') fun t => by
      rw [LinearMap.sub_apply, h, sub_self])
  have hqex : ∀ G : PDivGroup p O, ∃ q : latt G →ₛₗ[WittVector.fontaineTheta O p] G.dual.Lie,
      ∀ y t, q y (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t) := fun G => by
    choose x hx using fun y : latt G => y.2 0
    refine ⟨{ toFun := x
              map_add' := fun a b => hsep G _ _ (fun t => ?_)
              map_smul' := fun c a => hsep G _ _ (fun t => ?_) }, fun y t => (hx y t).symm⟩
    · rw [LinearMap.add_apply, ← hx, ← hx, ← hx]; exact ghost_add 0 (a.1 t) (b.1 t)
    · rw [LinearMap.smul_apply, ← hx, ← hx, smul_eq_mul]; exact ghost_mul 0 c (a.1 t)
  choose q hq using hqex

  have hadd : (lattFunctor p O).Additive :=
    { map_add := fun {X Y f g} => ModuleCat.hom_ext (LinearMap.ext fun y =>
        Subtype.ext (LinearMap.ext fun t => by
          change y.1 (tateMap _ _ O (f + g).unop t) =
            y.1 (tateMap _ _ O f.unop t) + y.1 (tateMap _ _ O g.unop t)
          rw [unop_add, map_add (f := _), LinearMap.add_apply, map_add (f := _)])) }

  have hred : ∃ (D : (PDivGroup p O)ᵒᵖ ⥤ ModuleCat.{0} O)
      (r : ∀ X : (PDivGroup p O)ᵒᵖ, latt X.unop →ₛₗ[WittVector.fontaineTheta O p] D.obj X),
      (∀ X, Function.Surjective (r X) ∧ ∀ m, r X m = 0 ↔ ∃ n, m = xi ε • n) ∧
      ∀ (X Y : (PDivGroup p O)ᵒᵖ) (f : X ⟶ Y) (m : latt X.unop),
        (D.map f).hom (r X m) = r Y (lattMap f.unop m) :=
    GlobalTheory.CompanionTheory.ModuleReduction.exists_reduction (Ainf p O) O
      (WittVector.fontaineTheta O p) hθ (xi ε) hker (PDivGroup p O)ᵒᵖ (lattFunctor p O)
  obtain ⟨D, r, hr, nr⟩ := hred

  have hπex : ∀ G : PDivGroup p O, ∃ π : D.obj (op G) →ₗ[O] G.dual.Lie,
      ∀ m, π (r (op G) m) = q G m := fun G =>
    GlobalTheory.CompanionTheory.Div.semilinear_factors_through_reduction (Ainf p O) O (WittVector.fontaineTheta O p) hθ
      (xi ε) hθξ _ (D.obj (op G)) G.dual.Lie (r (op G)) (q G) (hr (op G)).1 (hr (op G)).2
  choose π hπ using hπex

  have hιex := fun G : PDivGroup p O => GlobalTheory.T.exists_hodgeSequence_first_map_lattice p C v O hv ε hε G (hD G) (D.obj (op G))
    (r (op G)) (π G) (hr (op G)).1 (hr (op G)).2
    (fun y t => (LinearMap.congr_fun (hπ G y) (hodgeTate G t)).trans (hq G y t))
  choose ι hι using hιex
  have nr' : ∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : latt H),
      (D.map f.op).hom (r (op H) m) = r (op G) (lattMap f m) := fun G H f m => nr _ _ f.op m
  refine ⟨lattFunctor p O, D, φ, fun G => r (op G), ι, π, hadd, ?_⟩
  dsimp (config := { instances := true }) only [lattFunctor, Opposite.unop_op, Quiver.Hom.unop_op,
    ModuleCat.ofHom_apply, ModuleCat.hom_ofHom]
  refine ⟨?_, hφ2, ?_, fun G => hr (op G), nr', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun G => GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height p C v O hv ε hε G (hD G)
  · intro G H f m
    exact Subtype.ext (LinearMap.ext fun t =>
      (hφ1 H m (tateMap G H O f t)).trans (hφ1 G (lattMap f m) t).symm)
  · intro G
    refine ⟨(hι G).1, (hι G).2.1, fun x => ?_⟩
    obtain ⟨y, hy⟩ := (hLie G).2 x
    exact ⟨r (op G) y, (hπ G y).trans (hsep G _ _ fun t => (hq G y t).trans (hy t))⟩
  · intro G H f w
    exact GlobalTheory.T.pDivGroup_hodgeTateFirstMap_natural p C v O hv ε hε G H f (hD G) (hD H) (D.obj (op G)) (r (op G)) (D.obj (op H))
      (r (op H)) (D.map f.op).hom (ι G) (ι H) (hr (op G)).1 (hr (op G)).2 (nr' G H f)
      (hι G).2.2 (hι H).2.2 w
  · intro G H f x
    obtain ⟨m, rfl⟩ := (hr (op H)).1 x
    let ℓ := lieMap H.dual G.dual (dualHom G H f)
    have hqf : q G (lattMap f m) = ℓ (q H m) := hsep G _ _ fun t =>
      (hq G (lattMap f m) t).trans
        ((hq H m (tateMap G H O f t)).symm.trans (congrArg (q H m) (hodgeTate_tateMap f t)))
    exact (congrArg (π G) (nr' G H f m)).trans
      ((hπ G (lattMap f m)).trans (hqf.trans (congrArg ℓ (hπ H m).symm)))
  · obtain ⟨e, he⟩ := GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv p C v O hv ε hε
    exact ⟨e, fun m => (he (φ (const p O) m)).trans
      ((hφ1 (const p O) m (constGen p O)).trans (congrArg WittVector.frobenius (he m).symm))⟩
  · obtain ⟨e, he⟩ := GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one p C v O hv ε hε
    have : IsDomain (Ainf p O) := hdom
    have hμ : Sandwich.mu ε ≠ 0 := fun h => GlobalTheory.Dieudonne.not_dvd_mu hε1 (h ▸ dvd_zero _)
    refine ⟨e, fun m => mul_left_cancel₀ hμ ?_⟩
    have h1 : Sandwich.mu ε * e (φ _ m) = WittVector.frobenius (Sandwich.mu ε * e m) :=
      (he (φ (PDivGroup.mu p O) m)).trans
        ((hφ1 (PDivGroup.mu p O) m (epsTate hε)).trans (congrArg WittVector.frobenius (he m).symm))
    have h2 : WittVector.frobenius (Sandwich.mu ε * e m) =
        Sandwich.mu ε * (WittVector.frobenius (xi ε) * WittVector.frobenius (e m)) := by
      exact ((WittVector.frobenius : Ainf p O →+* Ainf p O).map_mul _ _).trans
        ((congrArg (· * WittVector.frobenius (e m)) (GlobalTheory.Dieudonne.frobenius_mu ε)).trans
          ((mul_assoc _ _ _).trans (mul_left_comm _ _ _)))
    exact h1.trans h2
  · change ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O),
        (∀ m, g (φ (PDivGroup.mu p O) m) = φ (const p O) (g m)) →
          ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g
    intro g hg
    refine GlobalTheory.T.existsUnique_muPInfinity_hodgeTate_lattice_map p C v O hv ε hε g ?_
    intro m m' hm t
    have e : m' = φ (PDivGroup.mu p O) m :=
      Subtype.ext (LinearMap.ext fun s => (hm s).trans (hφ1 (PDivGroup.mu p O) m s).symm)
    exact (congrArg (fun z : latt (PDivGroup.mu p O) => (g z).1 t) e).trans
      ((congrArg (fun z : latt (const p O) => z.1 t) (hg m)).trans (hφ1 (const p O) (g m) t))

end GlobalTheory.PDivLat
