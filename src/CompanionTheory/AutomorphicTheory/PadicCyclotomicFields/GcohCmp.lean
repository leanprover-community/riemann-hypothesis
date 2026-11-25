module

public import GroundTheory.ProfiniteCohomology.CupProducts
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import GroundTheory.ProfiniteCohomology.FilteredHomology
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohDefs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmpA, CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp

-- ===== clump member: CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmpA =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmpA", "h": "module\n\npublic import GroundTheory.ProfiniteCohomology.CupProducts\npublic import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem\npublic import GroundTheory.ProfiniteCohomology.FilteredHomology\nimport Mathlib.Algebra.Homology.ShortComplex.ModuleCat\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

section Core

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

theorem coc_inj (n : â„•) {x y : cocycles A n}
    (h : cochainOf A (cocycleÎ¹ A n x) = cochainOf A (cocycleÎ¹ A n y)) : x = y :=
  cocycleÎ¹_injective (cochainOf_injective h)

theorem exists_coc (n : â„•) (c : (Fin n â†’ G) â†’ A) (hc : IsLocallyConstant c)
    (hd : (inhomogeneousCochains.d A n).hom c = 0) :
    âˆƒ x : cocycles A n, cochainOf A (cocycleÎ¹ A n x) = c := by
  refine âŸ¨(cochainsComplex A).cyclesMk (mkCochain A c hc) (n + 1) (by simp) ?_, ?_âŸ©
  Â· apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans hd
  Â· exact congrArg (cochainOf A) ((cochainsComplex A).i_cyclesMk _ _ _ _)

theorem pi_succ_eq_zero_iff (n : â„•) (x : cocycles A (n + 1)) :
    cohomologyÏ€ A (n + 1) x = 0 â†” âˆƒ w : (Fin n â†’ G) â†’ A, IsLocallyConstant w âˆ§
      (inhomogeneousCochains.d A n).hom w = cochainOf A (cocycleÎ¹ A (n + 1) x) := by
  change ((cochainsComplex A).homologyÏ€ (n + 1)).hom x = 0 â†” _
  rw [homologyÏ€_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  Â· rintro âŸ¨w, hwâŸ©
    refine âŸ¨cochainOf A w, isLocallyConstant_cochainOf w, ?_âŸ©
    rw [â† cochainOf_d]
    exact congrArg (cochainOf A) hw
  Â· rintro âŸ¨w, hw, hâŸ©
    refine âŸ¨mkCochain A w hw, ?_âŸ©
    apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans h

theorem pi_zero_eq_zero_iff (x : cocycles A 0) :
    cohomologyÏ€ A 0 x = 0 â†” cochainOf A (cocycleÎ¹ A 0 x) = 0 := by
  change ((cochainsComplex A).homologyÏ€ 0).hom x = 0 â†” _
  rw [homologyÏ€_eq_zero_iff, CochainComplex.prev_nat_zero]
  have h0 : (cochainsComplex A).d 0 0 = 0 := (cochainsComplex A).shape 0 0 (by simp)
  rw [h0]
  constructor
  Â· rintro âŸ¨w, hwâŸ©
    exact (congrArg (cochainOf A) hw).symm
  Â· intro h
    refine âŸ¨0, ?_âŸ©
    apply cochainOf_injective (A := A)
    exact h.symm

theorem core_hom {Z : Type} [AddCommGroup Z] (n : â„•) (Ï† : Z â†’+ ((Fin n â†’ G) â†’ A))
    (hex : âˆ€ z, âˆƒ x : cocycles A n, cochainOf A (cocycleÎ¹ A n x) = Ï† z)
    (hsurj : âˆ€ x : cocycles A n, âˆƒ z, cochainOf A (cocycleÎ¹ A n x) = Ï† z) :
    âˆƒ f : Z â†’+ cohomology A n, Function.Surjective f âˆ§
      âˆ€ z x, cochainOf A (cocycleÎ¹ A n x) = Ï† z â†’ f z = cohomologyÏ€ A n x := by
  choose Ïˆ hÏˆ using hex
  have hadd : âˆ€ z z', Ïˆ (z + z') = Ïˆ z + Ïˆ z' := fun z z' => coc_inj A n (by
    rw [map_add (f := _), cochainOf_add, hÏˆ, hÏˆ, hÏˆ, map_add (f := _)])
  let f : Z â†’+ cohomology A n := AddMonoidHom.mk' (fun z => cohomologyÏ€ A n (Ïˆ z))
    (fun z z' => by rw [hadd, map_add (f := _)])
  have hf : âˆ€ z x, cochainOf A (cocycleÎ¹ A n x) = Ï† z â†’ f z = cohomologyÏ€ A n x := fun z x h => by
    have : Ïˆ z = x := coc_inj A n ((hÏˆ z).trans h.symm)
    change cohomologyÏ€ A n (Ïˆ z) = _
    rw [this]
  refine âŸ¨f, fun y => ?_, hfâŸ©
  obtain âŸ¨x, rflâŸ© := cohomologyÏ€_surjective A n y
  obtain âŸ¨z, hzâŸ© := hsurj x
  exact âŸ¨z, hf z x hzâŸ©

theorem core_quot {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] (B : Submodule R Z)
    (n : â„•) (Ï† : Z â†’+ ((Fin n â†’ G) â†’ A))
    (hex : âˆ€ z, âˆƒ x : cocycles A n, cochainOf A (cocycleÎ¹ A n x) = Ï† z)
    (hsurj : âˆ€ x : cocycles A n, âˆƒ z, cochainOf A (cocycleÎ¹ A n x) = Ï† z)
    (hB : âˆ€ z x, cochainOf A (cocycleÎ¹ A n x) = Ï† z â†’ (cohomologyÏ€ A n x = 0 â†” z âˆˆ B)) :
    âˆƒ e : (Z â§¸ B) â‰ƒ+ cohomology A n,
      âˆ€ z x, cochainOf A (cocycleÎ¹ A n x) = Ï† z â†’
        e (Submodule.Quotient.mk z) = cohomologyÏ€ A n x := by
  obtain âŸ¨f, hs, hfâŸ© := core_hom A n Ï† hex hsurj
  have hk : âˆ€ z, f z = 0 â†” z âˆˆ B := fun z => by
    obtain âŸ¨x, hxâŸ© := hex z
    rw [hf z x hx, hB z x hx]
  let g : (Z â§¸ B) â†’+ cohomology A n :=
    QuotientAddGroup.lift B.toAddSubgroup f (fun z hz => (hk z).2 hz)
  have hg : âˆ€ z, g (Submodule.Quotient.mk z) = f z := fun z => rfl
  refine âŸ¨AddEquiv.ofBijective g âŸ¨?_, ?_âŸ©, fun z x h => (hg z).trans (hf z x h)âŸ©
  Â· rw [injective_iff_map_eq_zero]
    intro q hq
    obtain âŸ¨z, rflâŸ© := Submodule.Quotient.mk_surjective B q
    rw [hg, hk] at hq
    exact (Submodule.Quotient.mk_eq_zero B).2 hq
  Â· intro y
    obtain âŸ¨z, rflâŸ© := hs y
    exact âŸ¨_, hg zâŸ©

end Core

theorem neg_one_pow_smul' {S V : Type} [Ring S] [AddCommGroup V] [Module S V] (j : â„•) (v : V) :
    (-1 : S) ^ j â€¢ v = (-1 : â„¤) ^ j â€¢ v := by
  rw [â† Int.cast_smul_eq_zsmul S]
  simp

section Cmp

variable {k G : Type} [CommRing k] [Group G]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  (rho : Representation R G M) (A : Rep.{0} k G) (e : M â‰ƒ+ A.V)
  (he : âˆ€ g m, e (rho g m) = A.Ï g (e m))

theorem dn_app (n : â„•) (f : (Fin n â†’ G) â†’ M) (g : Fin (n + 1) â†’ G) :
    dn rho n f g = rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : â„•) + 1) â€¢ f (Fin.contractNth j (Â· * Â·) g) := rfl

include he in
theorem d_comp (n : â„•) (f : (Fin n â†’ G) â†’ M) :
    (inhomogeneousCochains.d A n).hom (fun s => e (f s)) = fun s => e (dn rho n f s) := by
  funext s

  rw [inhomogeneousCochains.d_hom_apply, dn_app, map_add (f := _), map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_one_pow_smul' (S := k), neg_one_pow_smul' (S := R), map_zsmul]

theorem dn_zero (f : (Fin 0 â†’ G) â†’ M) (s : Fin 1 â†’ G) :
    dn rho 0 f s = rho (s 0) (f default) - f default := by
  have h : âˆ€ t, f t = f default := fun t => congrArg f (Subsingleton.elim _ _)
  rw [dn_app]
  simp [h, sub_eq_add_neg]

theorem dn_one (f : G â†’ M) (s : Fin 2 â†’ G) :
    dn rho 1 (fun t => f (t 0)) s = rho (s 0) (f (s 1)) - f (s 0 * s 1) + f (s 0) := by
  rw [dn_app]
  simp [Fin.sum_univ_succ, Fin.contractNth, sub_eq_add_neg, add_assoc]

theorem dn_two (f : G Ã— G â†’ M) (s : Fin 3 â†’ G) :
    dn rho 2 (fun t => f (t 0, t 1)) s =
      rho (s 0) (f (s 1, s 2)) - f (s 0 * s 1, s 2) + f (s 0, s 1 * s 2) - f (s 0, s 1) := by
  rw [dn_app]
  have h3 : (-1 : R) ^ 3 = -1 := by norm_num
  simp [h3, Fin.sum_univ_succ, Fin.contractNth, sub_eq_add_neg, add_assoc]

end Cmp

end CompanionTheory.LocalTateOrthogonality.Gcoh
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmpA =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohDefs\npublic import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmpA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem gcRep : SgcRep := by
  intro G _ _ _ R _ M _ _ _ _ rho hrho
  letI : Module (ULift.{0} â„¤) M := Module.compHom M (ULift.ringEquiv : ULift.{0} â„¤ â‰ƒ+* â„¤).toRingHom
  let Ïƒ : Representation (ULift.{0} â„¤) G M :=
    { toFun := fun g =>
        { toFun := rho g
          map_add' := map_add _
          map_smul' := fun c m => map_zsmul (rho g) c.down m }
      map_one' := LinearMap.ext fun m => by
        change rho 1 m = m
        rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => by
        change rho (g * h) m = rho g (rho h m)
        rw [map_mul]; rfl }
  refine âŸ¨Rep.of Ïƒ, âŸ¨fun a => ?_âŸ©, AddEquiv.refl M, fun g m => rflâŸ©
  have hc : Continuous fun g : G => rho g (a : M) :=
    hrho.comp (continuous_id.prodMk continuous_const)
  exact (isOpen_discrete {(a : M)}).preimage hc

attribute [local instance 2000] Rep.hV2

section

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  (A : Rep.{0} k G) (e : M â‰ƒ+ A.V)

omit [IsTopologicalGroup G] in
theorem lc_of_cont {X : Type} [TopologicalSpace X] {f : X â†’ M} (hf : Continuous f) :
    IsLocallyConstant fun s => e (f s) :=
  ((IsLocallyConstant.iff_continuous f).2 hf).comp e

omit [IsTopologicalGroup G] in
theorem cont_of_lc {X : Type} [TopologicalSpace X] {f : X â†’ A.V} (hf : IsLocallyConstant f) :
    Continuous fun s => e.symm (f s) :=
  (hf.comp e.symm).continuous

end

theorem gcn : Sgcn := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he n
  let Ï† : Zn rho n â†’+ ((Fin n â†’ G) â†’ A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 s)) (fun z z' => funext fun s => map_add e _ _)
  have hÏ† : âˆ€ z s, Ï† z s = e (z.1 s) := fun _ _ => rfl
  obtain âŸ¨e', -âŸ© := core_quot A ((Bn rho n).comap (Zn rho n).subtype) n Ï†
    (fun z => exists_coc A n _ (lc_of_cont A e z.2.1) (by
      have hz : dn rho n z.1 = 0 := z.2.2
      refine (d_comp rho A e he n z.1).trans ?_
      funext s
      rw [hz]
      exact map_zero e))
    (fun x => by
      refine âŸ¨âŸ¨fun s => e.symm (cochainOf A (cocycleÎ¹ A n x) s),
        cont_of_lc A e (isLocallyConstant_cochainOf _), ?_âŸ©, ?_âŸ©
      Â· have h := d_comp rho A e he n fun s => e.symm (cochainOf A (cocycleÎ¹ A n x) s)
        simp only [AddEquiv.apply_symm_apply] at h
        rw [d_cocycleÎ¹] at h
        change dn rho n _ = 0
        funext s
        apply e.injective
        rw [â† congrFun h s]
        exact (map_zero e).symm
      Â· funext s
        exact (e.apply_symm_apply _).symm)
    (fun z x hx => by
      cases n with
      | zero =>
        rw [pi_zero_eq_zero_iff, hx]
        change _ â†” z.1 = 0
        constructor
        Â· intro h
          funext s
          exact e.map_eq_zero_iff.1 (congrFun h s)
        Â· intro h
          funext s
          rw [hÏ†, h]
          exact map_zero e
      | succ n =>
        rw [pi_succ_eq_zero_iff, hx]
        constructor
        Â· rintro âŸ¨w, hw, hâŸ©
          refine âŸ¨fun s => e.symm (w s), cont_of_lc A e hw, ?_âŸ©
          have h' := d_comp rho A e he n fun s => e.symm (w s)
          simp only [AddEquiv.apply_symm_apply] at h'
          funext s
          apply e.injective
          exact (congrFun h' s).symm.trans (congrFun h s)
        Â· rintro âŸ¨c, hc, hâŸ©
          refine âŸ¨fun s => e (c s), lc_of_cont A e hc, (d_comp rho A e he n c).trans ?_âŸ©
          funext s
          rw [h]
          rfl)
  exact âŸ¨e'âŸ©

theorem gc0 : Sgc0 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let Ï† : H0 rho â†’+ ((Fin 0 â†’ G) â†’ A) :=
    AddMonoidHom.mk' (fun z _ => e z.1) (fun z z' => funext fun s => map_add e _ _)
  have hex : âˆ€ z, âˆƒ x : cocycles A 0, cochainOf A (cocycleÎ¹ A 0 x) = Ï† z := fun z =>
    exists_coc A 0 _ (IsLocallyConstant.const _) (by
      refine (d_comp rho A e he 0 fun _ => z.1).trans ?_
      funext s
      rw [dn_zero, z.2 (s 0), sub_self]
      exact map_zero e)
  obtain âŸ¨f, hs, hfâŸ© := core_hom A 0 Ï† hex (fun x => by
    refine âŸ¨âŸ¨e.symm (cochainOf A (cocycleÎ¹ A 0 x) default), fun g => ?_âŸ©, ?_âŸ©
    Â· have h := d_comp rho A e he 0 fun s => e.symm (cochainOf A (cocycleÎ¹ A 0 x) s)
      simp only [AddEquiv.apply_symm_apply] at h
      rw [d_cocycleÎ¹] at h
      have h' := congrFun h (fun _ => g)
      rw [dn_zero] at h'
      exact sub_eq_zero.1 (e.map_eq_zero_iff.1 h'.symm)
    Â· funext s
      rw [Subsingleton.elim s default]
      exact (e.apply_symm_apply _).symm)
  refine âŸ¨AddEquiv.ofBijective f âŸ¨?_, hsâŸ©, fun m x h => hf m x (funext h)âŸ©
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain âŸ¨x, hxâŸ© := hex z
  rw [hf z x hx, pi_zero_eq_zero_iff, hx] at hz
  exact Subtype.ext (e.map_eq_zero_iff.1 (congrFun hz default))

theorem gc1 : Sgc1 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let Ï† : Z1 rho â†’+ ((Fin 1 â†’ G) â†’ A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 (s 0))) (fun z z' => funext fun s => map_add e _ _)
  have hex : âˆ€ z, âˆƒ x : cocycles A 1, cochainOf A (cocycleÎ¹ A 1 x) = Ï† z := fun z =>
    exists_coc A 1 _ (lc_of_cont A e (z.2.1.comp (continuous_apply 0))) (by
      refine (d_comp rho A e he 1 fun s => z.1 (s 0)).trans ?_
      funext s
      rw [dn_one, z.2.2 (s 0) (s 1)]
      rw [show âˆ€ a b : M, b - (a + b) + a = 0 from fun a b => by abel]
      exact map_zero e)
  have hv : âˆ€ s : Fin 1 â†’ G, s = fun _ => s 0 := fun s => funext fun i => by
    rw [Subsingleton.elim i 0]
  obtain âŸ¨e', he'âŸ© := core_quot A ((B1 rho).comap (Z1 rho).subtype) 1 Ï† hex
    (fun x => by
      have hx : cochainOf A (cocycleÎ¹ A 1 x) =
          fun s => e (e.symm (cochainOf A (cocycleÎ¹ A 1 x) fun _ => s 0)) := by
        funext s
        rw [e.apply_symm_apply, â† hv]
      refine âŸ¨âŸ¨fun g => e.symm (cochainOf A (cocycleÎ¹ A 1 x) fun _ => g),
        (cont_of_lc A e (isLocallyConstant_cochainOf _)).comp
          (continuous_pi fun _ => continuous_id), fun g g' => ?_âŸ©, hxâŸ©
      have h := d_comp rho A e he 1 fun s => e.symm (cochainOf A (cocycleÎ¹ A 1 x) fun _ => s 0)
      rw [â† hx, d_cocycleÎ¹] at h
      have h' := congrFun h ![g, g']
      rw [dn_one rho (fun g => e.symm (cochainOf A (cocycleÎ¹ A 1 x) fun _ => g))] at h'
      have h2 := e.map_eq_zero_iff.1 h'.symm
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [â† sub_eq_zero, â† neg_eq_zero, â† h2]
      abel)
    (fun z x hx => by
      rw [pi_succ_eq_zero_iff, hx]
      constructor
      Â· rintro âŸ¨w, hw, hâŸ©
        refine âŸ¨e.symm (w default), ?_âŸ©
        have h' := d_comp rho A e he 0 fun s => e.symm (w s)
        simp only [AddEquiv.apply_symm_apply] at h'
        funext g
        apply e.injective
        have h2 := (congrFun h' fun _ => g).symm.trans (congrFun h fun _ => g)
        rw [dn_zero] at h2
        exact h2
      Â· rintro âŸ¨m, hâŸ©
        refine âŸ¨fun _ => e m, IsLocallyConstant.const _, (d_comp rho A e he 0 fun _ => m).trans ?_âŸ©
        funext s
        rw [dn_zero]
        exact congrArg e (congrFun h (s 0)))
  refine âŸ¨e', fun z => ?_, fun z x h => he' z x (funext h)âŸ©
  obtain âŸ¨x, hxâŸ© := hex z
  exact âŸ¨x, congrFun hxâŸ©

theorem gc2 : Sgc2 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let Ï† : Z2 rho â†’+ ((Fin 2 â†’ G) â†’ A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 (s 0, s 1))) (fun z z' => funext fun s => map_add e _ _)
  have hex : âˆ€ z, âˆƒ x : cocycles A 2, cochainOf A (cocycleÎ¹ A 2 x) = Ï† z := fun z =>
    exists_coc A 2 _
      (lc_of_cont A e (z.2.1.comp ((continuous_apply 0).prodMk (continuous_apply 1)))) (by
      refine (d_comp rho A e he 2 fun s => z.1 (s 0, s 1)).trans ?_
      funext s
      rw [dn_two, z.2.2 (s 0) (s 1) (s 2)]
      exact map_zero e)
  have hv : âˆ€ s : Fin 1 â†’ G, s = fun _ => s 0 := fun s => funext fun i => by
    rw [Subsingleton.elim i 0]
  have hv2 : âˆ€ s : Fin 2 â†’ G, s = ![s 0, s 1] := fun s => funext fun i => by
    fin_cases i <;> rfl
  obtain âŸ¨e', he'âŸ© := core_quot A ((B2 rho).comap (Z2 rho).subtype) 2 Ï† hex
    (fun x => by
      have hx : cochainOf A (cocycleÎ¹ A 2 x) =
          fun s => e (e.symm (cochainOf A (cocycleÎ¹ A 2 x) ![s 0, s 1])) := by
        funext s
        rw [e.apply_symm_apply, â† hv2]
      refine âŸ¨âŸ¨fun p => e.symm (cochainOf A (cocycleÎ¹ A 2 x) ![p.1, p.2]),
        (cont_of_lc A e (isLocallyConstant_cochainOf _)).comp
          (continuous_pi fun i => by
            fin_cases i
            Â· exact continuous_fst
            Â· exact continuous_snd), fun g g' g'' => ?_âŸ©, hxâŸ©
      have h := d_comp rho A e he 2 fun s => e.symm (cochainOf A (cocycleÎ¹ A 2 x) ![s 0, s 1])
      rw [â† hx, d_cocycleÎ¹] at h
      have h' := congrFun h ![g, g', g'']
      rw [dn_two rho (fun p => e.symm (cochainOf A (cocycleÎ¹ A 2 x) ![p.1, p.2]))] at h'
      exact e.map_eq_zero_iff.1 h'.symm)
    (fun z x hx => by
      rw [pi_succ_eq_zero_iff, hx]
      constructor
      Â· rintro âŸ¨w, hw, hâŸ©
        refine âŸ¨fun g => e.symm (w fun _ => g),
          (cont_of_lc A e hw).comp (continuous_pi fun _ => continuous_id), ?_âŸ©
        have hw' : w = fun s => e (e.symm (w fun _ => s 0)) := by
          funext s
          rw [e.apply_symm_apply, â† hv]
        have h' := d_comp rho A e he 1 fun s => e.symm (w fun _ => s 0)
        rw [â† hw'] at h'
        funext p
        apply e.injective
        have h2 := (congrFun h' ![p.1, p.2]).symm.trans (congrFun h ![p.1, p.2])
        rw [dn_one rho (fun g => e.symm (w fun _ => g))] at h2
        exact h2
      Â· rintro âŸ¨c, hc, hâŸ©
        refine âŸ¨fun s => e (c (s 0)), lc_of_cont A e (Continuous.comp hc (continuous_apply 0)),
          (d_comp rho A e he 1 fun s => c (s 0)).trans ?_âŸ©
        funext s
        rw [dn_one]
        exact congrArg e (congrFun h (s 0, s 1)))
  refine âŸ¨e', fun z => ?_, fun z x h => he' z x (funext h)âŸ©
  obtain âŸ¨x, hxâŸ© := hex z
  exact âŸ¨x, congrFun hxâŸ©

end CompanionTheory.LocalTateOrthogonality.Gcoh
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp =====
