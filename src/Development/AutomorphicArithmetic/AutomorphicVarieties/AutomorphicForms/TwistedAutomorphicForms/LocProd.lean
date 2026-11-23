module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

private noncomputable def UpperTheory.V.Af.Tw.compAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def UpperTheory.V.Af.Tw.infPart (K : Type) [Field K] [NumberField K] :
    AdeleRing (𝓞 K) K →* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem UpperTheory.V.Af.Tw.loc_same {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_same _ _ _

private theorem UpperTheory.V.Af.Tw.loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 w = 1 := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

theorem UpperTheory.V.Af.Tw.locProd :
    UpperTheory.V.Af.Tw.LocProd := by
  unfold UpperTheory.V.Af.Tw.LocProd
  intro F L _ _ _ _ _ v x
  classical
  let y : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ := fun w =>
    Units.map (finiteCompletionMap F L w).toMonoidHom
      (Units.map (UpperTheory.V.Af.Tw.compAt F (HeightOneSpectrum.under (𝓞 F) w)) (localIdele F v x))
  have hy : ∀ w, ((y w : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      finiteCompletionMap F L w ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w)) :=
    fun w => rfl
  have hmem : ∀ w : HeightOneSpectrum (𝓞 L),
      w ∈ aboveF F v ↔ HeightOneSpectrum.under (𝓞 F) w = v :=
    fun w => by
      unfold aboveF
      simp
  have key : ∀ a b : AdeleRing (𝓞 L) L, UpperTheory.V.Af.Tw.infPart L a = UpperTheory.V.Af.Tw.infPart L b →
      (∀ w, UpperTheory.V.Af.Tw.compAt L w a = UpperTheory.V.Af.Tw.compAt L w b) → a = b :=
    fun a b h1 h2 => Prod.ext h1 (RestrictedProduct.ext _ _ h2)
  refine ⟨y, ?_, ?_⟩
  · apply Units.ext
    rw [Units.coe_prod]
    apply key
    · rw [map_prod]
      have h1 : ∀ w, UpperTheory.V.Af.Tw.infPart L ((localIdele L w (y w)).val) = 1 := fun w => rfl
      simp only [h1, Finset.prod_const_one]
      show infiniteAdeleMap F L 1 = 1
      exact map_one _
    · intro w'
      rw [map_prod]
      show finiteCompletionMap F L w' ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w')) =
        ∏ w ∈ aboveF F v, (localIdele L w (y w)).val.2 w'
      by_cases hw' : HeightOneSpectrum.under (𝓞 F) w' = v
      · rw [Finset.prod_eq_single w']
        · rw [UpperTheory.V.Af.Tw.loc_same, hy]
        · intro b _ hb
          exact UpperTheory.V.Af.Tw.loc_ne (Ne.symm hb) _
        · intro h
          exact absurd ((hmem w').mpr hw') h
      · rw [UpperTheory.V.Af.Tw.loc_ne hw', map_one, Finset.prod_eq_one]
        intro b hb
        exact UpperTheory.V.Af.Tw.loc_ne (fun h => hw' (by rw [h]; exact (hmem b).mp hb)) _
  · intro hunr hx w hw
    subst hw
    unfold IsUnifAt at hx ⊢
    rw [hy, UpperTheory.V.Af.Tw.loc_same, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, hunr w rfl, pow_one]
    exact hx
