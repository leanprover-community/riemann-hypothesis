import Formalism.LocalToGlobal.Divisibility.NumbersLink
import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ColumnBoundOfPaths

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AtG.EntryG

open Formalism.L2.Col (Fields Sp HomE homAt divLat IsSdLat)
open Formalism.L2.Ker (Amb DVar)
open Formalism.L2.AlgTh (KerStd SplitS JetAtSplit IsQInt GAt)
open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

section Terms

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ}

structure Term (X : Fields) (p : ℕ) [Fact p.Prime] (a b : ℕ) where

  coef : ℂ_[p]

  scal : X.K

  xi : X.K

  S : Finset (HeightOneSpectrum (𝓞 X.E))

  N : Submodule (𝓞 X.E) (Sp X.E a)

  N' : Submodule (𝓞 X.E) (Sp X.E b)

  c' : ℕ

  x : HomE X.E a b

  m : DVar X.Tau a b →₀ ℕ

def Term.val (A : Amb X) (ι : ℂ ≃+* ℂ_[p]) (T : Term X p a b) : ℂ_[p] :=
  T.coef * ι (A.σ₀ T.scal) * ι (A.σ₀ T.xi) * ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))

def Term.Ok (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (T : Term X p a b) : Prop :=
  ‖T.coef‖ ≤ 1 ∧ ‖ι (A.σ₀ T.scal)‖ ≤ 1 ∧ ‖ι (A.σ₀ T.xi)‖ ≤ ‖(p : ℂ_[p])‖ ^ e ∧
  KerStd A T.N T.N' a₀ b₀ c₀ ha hd lam hlam p ι ∧ IsSdLat T.N ∧ IsSdLat T.N' ∧ A.LaHyp a b T.S ∧ SplitS A T.S p ϖ pE ∧
  0 < T.c' ∧ ¬ p ∣ T.c' ∧ T.x ∈ divLat T.c' (homAt T.S T.N T.N') ∧ T.m.degree = D

def IsEntryG (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) (y : ℂ_[p]) : Prop :=
  ∃ (n : ℕ) (T : Fin n → Term X p a b), y = ∑ k, (T k).val A ι ∧ ∀ k, (T k).Ok A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e

theorem isEntryG_zero (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) : IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e a b 0 :=
  ⟨0, Fin.elim0, by simp, fun k => k.elim0⟩

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ :=
  norm_pos_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

theorem term_bound (hJ : JetAtSplit) (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0)
    (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (hp2 : p ≠ 2) (hpd : ¬ p ∣ A.d) (hϖ : IsQInt A.d ϖ) (hϖϖ : ϖ * conj ϖ = (p : ℂ))
    {D : ℕ} {e : ℝ} {T : Term X p a b} (hT : T.Ok A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e) :
    ‖T.val A ι‖ * ‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) ≤ 1 := by
  obtain ⟨hc, hs, hx, hK, hN, hN', hLa, hS, hc0, hcp, hxd, hm⟩ := hT
  have hj := hJ X A a b T.S T.N T.N' a₀ b₀ c₀ ha hd lam hlam p ι hp2 hpd hK hN hN' hLa ϖ pE hϖ hϖϖ hS T.c' T.x hc0 hcp hxd T.m
  rw [hm] at hj
  have hp0 := norm_p_pos (p := p)
  have hval : ‖T.val A ι‖ ≤ ‖(p : ℂ_[p])‖ ^ e * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ := by
    unfold Term.val
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖T.coef‖ * ‖ι (A.σ₀ T.scal)‖ ≤ 1 :=
      (mul_le_mul hc hs (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1))
    calc ‖T.coef‖ * ‖ι (A.σ₀ T.scal)‖ * ‖ι (A.σ₀ T.xi)‖ * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖
        ≤ 1 * ‖(p : ℂ_[p])‖ ^ e * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ := by
          gcongr
      _ = ‖(p : ℂ_[p])‖ ^ e * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ := by ring
  have hsplit : ‖(p : ℂ_[p])‖ ^ e * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) =
      ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) := by
    rw [← Real.rpow_add hp0, add_sub_cancel, Real.rpow_natCast]
  have hR0 : 0 ≤ ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) := Real.rpow_nonneg hp0.le _
  calc ‖T.val A ι‖ * ‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e)
      ≤ (‖(p : ℂ_[p])‖ ^ e * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖) * ‖ι (conj ϖ)‖ ^ D *
          ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) := by gcongr
    _ = ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ * ‖ι (conj ϖ)‖ ^ D *
          (‖(p : ℂ_[p])‖ ^ e * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e)) := by ring
    _ = ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ * ‖ι (conj ϖ)‖ ^ D *
          ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) := by rw [hsplit]
    _ ≤ 1 := hj

theorem entry_bound (hJ : JetAtSplit) (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0)
    (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (hp2 : p ≠ 2) (hpd : ¬ p ∣ A.d) (hϖ : IsQInt A.d ϖ) (hϖϖ : ϖ * conj ϖ = (p : ℂ))
    {D : ℕ} {e : ℝ} {y : ℂ_[p]} (hy : IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e a b y) :
    ‖y‖ * ‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) ≤ 1 := by
  obtain ⟨n, T, rfl, hT⟩ := hy
  have hp0 := norm_p_pos (p := p)
  have hϖ0 : conj ϖ ≠ 0 := by
    intro h0
    have h1 : (p : ℂ) = 0 := by rw [← hϖϖ, h0, mul_zero]
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
  have hι0 : 0 < ‖ι (conj ϖ)‖ := norm_pos_iff.mpr (by simpa using hϖ0)
  have hc0 : 0 < ‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) :=
    mul_pos (pow_pos hι0 _) (Real.rpow_pos_of_pos hp0 _)
  have hterm : ∀ k, ‖(T k).val A ι‖ ≤ (‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e))⁻¹ := by
    intro k
    have h := term_bound hJ A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE hp2 hpd hϖ hϖϖ (hT k)
    rw [mul_assoc] at h
    have h2 := (le_div_iff₀ hc0).mpr h
    rwa [one_div] at h2
  have hsum := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (inv_nonneg.mpr hc0.le) (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [mul_assoc]
  calc ‖∑ k, (T k).val A ι‖ * (‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e))
      ≤ (‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e))⁻¹ *
          (‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e)) :=
        mul_le_mul_of_nonneg_right hsum hc0.le
    _ = 1 := inv_mul_cancel₀ hc0.ne'

end Terms

section Place

variable {X : Fields}

def EntryG (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ϖ : ℂ) (pE : 𝓞 X.E)
    {Bs : DefBase X.K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 X.K) (Fin (Dc.a u) → X.K))
    (w : HeightOneSpectrum (𝓞 X.K)) (g : ℕ) [Fact g.Prime] (Dg : Bs.J → ℕ) (ab : Bs.J → ℕ × ℕ) (e : Bs.J → ℝ) : Prop :=
  ∃ (ι : ℂ ≃+* ℂ_[g]) (Y : PathData X.K g Bs.J (Fin (Dc.a u) → X.K) (Fin (Df.nV t) → X.K)) (D : ℕ) (j1 : Bs.J),
    EmbAt w g ((ι : ℂ →+* ℂ_[g]).comp A.σ₀) ∧
    IsExpansion Y ((ι : ℂ →+* ℂ_[g]).comp A.σ₀) (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → X.K)) (Df.Mt t : Set (Fin (Df.nV t) → X.K)) ∧
    ColsInt Y w (Nu : Set (Fin (Dc.a u) → X.K)) ∧ RowsInt Y w (Df.Mt t : Set (Fin (Df.nV t) → X.K)) ∧
    LastInt Y ∧ UnitsInt Y ∧ StabDvd Y D j1 ∧ ¬ g ∣ D ∧
    ∀ π j, IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE (Dg j) (e j) (ab j).1 (ab j).2 (Y.e π j)



end Place

section Record

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Indef

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

def EntryGRec (hX : X.Ok) {Bs : DefBase X.K} (Df : DefSide Bs) {P : LevFam X.E X.K Rk.r Pr.vGs}
    (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m} (mu : Bs.Tup → Tup X.F X.E X.K Sg)
    (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K)))
    (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word)
    (b : ∀ t, Mem → (L t).β (m2 + 1)) (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < Am.d) (lam : ℂ) (hlam : lam ≠ 0) (ϖ : ℂ) (pE : 𝓞 X.E)
    (u : Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd u)) → X.K)) (w : HeightOneSpectrum (𝓞 X.K))
    (g : ℕ) [Fact g.Prime] (Dg : Bs.J → ℕ) (ab : Bs.J → ℕ × ℕ) (e : Bs.J → ℝ) : Prop :=
  EntryG Am a₀ b₀ c₀ ha hd lam hlam ϖ pE (colFace hX Df Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF ev) u t Nu w g
    Dg ab e



end Record

end Formalism.L2.AtG.EntryG
