module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.SmulMemTrpSet
public import Formalism.LocalToGlobal.Columns.LocWLemmas
public import Formalism.LocalToGlobal.Columns.AtTLemmas
public import Formalism.LocalToGlobal.Columns.AtTRank
public import Formalism.LogVandermondeBounds.FinrankFiberSumZero

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.LogVandermondeBounds

section CoordLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
  {N : Submodule (𝓞 E) (Sp E n)}

variable {co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)}

end CoordLemmas

section FibLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} {P : ST} {q : 𝓞 E} {co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal)}

end FibLemmas

section FibModel

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} {P : ST} {q : 𝓞 E} {co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal)}

end FibModel

section Exists

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem intAt_algebraMap_ow (P : HeightOneSpectrum (𝓞 E)) (r : Ow P) : IntAt P (algebraMap (Ow P) E r) := by
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq P.asIdeal.primeCompl r
  refine ⟨a, t, t.2, ?_⟩
  rw [IsScalarTower.algebraMap_apply (𝓞 E) (Ow P) E, ← map_mul, mul_comm, IsLocalization.mk'_spec,
    ← IsScalarTower.algebraMap_apply]

theorem exists_locBasis (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsFullLattice E N) :
    ∃ β : Module.Basis (Fin n) E (Sp E n), (∀ i, β i ∈ localization₂ P.asIdeal N) ∧
      ∀ y ∈ localization₂ P.asIdeal N, ∀ i, IntAt P (β.repr y i) := by
  classical
  obtain ⟨ι, _, b, bK, hb⟩ := exists_basis_atW P hN.toIsLattice.fg hN.span_eq_top
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨bK.reindex e, fun i => ?_, fun y hy i => ?_⟩
  · rw [Module.Basis.reindex_apply, hb]
    exact (mem_locP _ _ _).2 (mem_atW_iff.1 (b (e.symm i)).2)
  · have hy' : y ∈ atW P N := mem_atW_iff.2 ((mem_locP _ _ _).1 hy)
    have h1 : (∑ j, b.repr ⟨y, hy'⟩ j • b j) = (⟨y, hy'⟩ : atW P N) := b.sum_repr _
    have h2 : y = ∑ j, algebraMap (Ow P) E (b.repr ⟨y, hy'⟩ j) • bK j := by
      have h3 := congrArg (fun z : atW P N => (z : Sp E n)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      refine h3.symm.trans ?_
      exact Finset.sum_congr rfl fun j _ => by rw [hb, ow_smul_def]
    have h4 : bK.repr y (e.symm i) = algebraMap (Ow P) E (b.repr ⟨y, hy'⟩ (e.symm i)) := by
      have h5 := congrArg (fun z => bK.repr z (e.symm i)) h2
      simp only [Module.Basis.repr_sum_self] at h5
      exact h5
    rw [Module.Basis.repr_reindex_apply, h4]
    exact intAt_algebraMap_ow P _

end Exists

section Apply

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Apply

section Dict

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  {C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))} {Λ : LevFam X.E X.K n SG}

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E} {d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)}
  {R : Type} [CommRing R] {σ : X.K →+* R}

end Dict

section T1

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E}

section Lin

variable {C Λ} {d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)}
  {R : Type} [CommRing R] {σ : X.K →+* R}

end Lin

end T1

section T7

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E}

section DictC

variable {C Λ} {d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)} {σ : X.K →+* ℂ}

end DictC

end T7

section ColsT1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

variable (Ps : CharT X Pr)

end ColsT1

section AdjA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end AdjA

section AdjB
variable {X : Fields}

end AdjB

section AdjC
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end AdjC

section AdjD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end AdjD

section AdjF
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end AdjF

section RamStable

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end RamStable

end Formalism.L2.Col
