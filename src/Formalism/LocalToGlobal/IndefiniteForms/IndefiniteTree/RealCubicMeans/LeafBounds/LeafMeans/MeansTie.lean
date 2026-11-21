import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.PackedMeans.IndexMeans.MeansPf
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

noncomputable section

open Finset

namespace IxMeans.MeansTie

def kap (N p : ℕ) (i : Fin N) : ℝ :=
  if (i : ℕ) < p then (N : ℝ) - 2 * p + 1 + 2 * (i : ℕ) else -(2 * (p : ℝ)) - N + 1 + 2 * (i : ℕ)

def de (N p : ℕ) (i : Fin N) : ℝ := if (i : ℕ) < p then 0 else -1

def gap {N : ℕ} (v : Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k + 1 < N then v ⟨k, by omega⟩ - v ⟨k + 1, h⟩ else 0

def anchored {N : ℕ} (G : ℕ → ℝ) (A : ℕ) (i : Fin N) : ℝ :=
  if (i : ℕ) ≤ A then ∑ k ∈ Ico (i : ℕ) A, G k else -∑ k ∈ Ico A (i : ℕ), G k

def uMinus (N p : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ := fun i => u i - c0 * de N p i

def firstVectorGaps (N p T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) (k : ℕ) : ℝ :=
  ((⌊gap (fun i => uMinus N p c0 u i - kap N p i) k / ((T : ℝ) + D + 1)⌋ : ℤ) : ℝ)

def firstGapVector (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ := anchored (firstVectorGaps N p T D c0 u) A

def upDef (N p A T D : ℕ) (c0 : ℝ) (u : Fin N → ℝ) : Fin N → ℝ :=
  fun i => firstGapVector N p A T D c0 u i - 3 * N * de N p i








structure Leaves (Tau : Type) where

  dE : ℕ

  level : ℕ

  q1 : ℕ

  d : ℕ

  g1 : ℕ

  g2 : ℕ

  rr : ℕ

  rr' : ℕ

  r0 : ℕ

  P0 : ℝ

  logmu : ℝ

  cubicPeriodConstant : ℝ

  c1 : ℝ

  Nc : ℕ

  bigp : Tau → ℕ

  A : ℕ

  eloc : ℕ → Finset ℝ

def cppDef (q : ℕ) : ℝ := if q = 2 then 1 else 1 / ((q : ℝ) - 1)

def XWDef {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι) : ℝ :=
  66 * P.L + (P.nc : ℝ) * P.f * P.N * Real.log P.rd

def kpDef {Tau ι : Type} [Fintype Tau] [Fintype ι] (P : MeansPack Tau ι) (q : ℕ) : ℝ :=
  (P.nc : ℝ) * P.f * P.N * P.vdd q / 2

namespace Leaves

variable {Tau ι : Type} [Fintype Tau] [Fintype ι] (Lv : Leaves Tau) (P : MeansPack Tau ι)

def rdDef : ℝ := (Lv.dE : ℝ) ^ ((1 : ℝ) / (2 * (P.f : ℝ)))

def vddDef (q : ℕ) : ℝ := (padicValNat q Lv.dE : ℝ) / (2 * (P.f : ℝ))

def SBDef : Finset ℕ := ((range (⌊P.B0⌋₊ + 1)).filter Nat.Prime) ∪ (2 * Lv.dE * Lv.level).primeFactors

def PPeDef : ℝ :=
  3 / 2 * (P.f : ℝ) * (P.N : ℝ) ^ 4 * P.L
    + (((P.f : ℝ) * (P.N : ℝ) ^ 2 + 3) * P.f * P.N * Real.log P.rd + 3 * Real.log ((2 * Lv.q1 * Lv.d : ℕ) : ℝ))
    + (3 * Real.log ((Lv.g1 * Lv.g2 : ℕ) : ℝ) + Real.log ((Lv.rr * Lv.rr' : ℕ) : ℝ))

def Xde : ℝ := Lv.logmu + 3 * (P.D : ℝ) * P.L

def Psup : ℝ := 1 / 2 * Real.log (Lv.r0 : ℝ) + Lv.P0 + 2 * (P.f : ℝ) * (P.N : ℝ) ^ 2

def Ptau0 : ℝ := 1 / 2 * Real.log (Lv.r0 : ℝ) + Real.log (Real.exp (Lv.Xde P) + 1) + Lv.Psup P

def PPA : ℝ := 3 * (P.D : ℝ) + 3 * Lv.cubicPeriodConstant

def PinfDef : ℝ :=
  2 * Lv.Ptau0 P + Lv.PPA P + 2 * (P.f : ℝ) * P.N * Lv.c1 + 7 * (P.f : ℝ) * (P.N : ℝ) ^ 2 + 2 * Real.log (Lv.Nc : ℝ)

def rnd (q : ℕ) : ℝ :=
  (if q ∣ 2 * Lv.dE * Lv.level then 1 else 0) + (if q ∣ 2 * Lv.q1 * Lv.d then kpDef P q + 1 else 0)

def eDef (q : ℕ) : ℝ := (Lv.eloc q).fold max 0 (fun x => x + Lv.rnd P q)

end Leaves

variable {Tau ι : Type} [Fintype Tau] [Fintype ι]

structure DefTie (P : MeansPack Tau ι) (Lv : Leaves Tau) : Prop where
  hu1 : ∀ τ, P.u1 τ = firstGapVector P.N (Lv.bigp τ) Lv.A P.T P.D P.c0 (P.u τ)
  hup : ∀ τ, P.up τ = upDef P.N (Lv.bigp τ) Lv.A P.T P.D P.c0 (P.u τ)
  hrd : P.rd = Lv.rdDef P
  hvdd : ∀ q, P.vdd q = Lv.vddDef P q
  hcpp : ∀ q, P.cpp q = cppDef q
  hSB : P.SB = Lv.SBDef P
  hPPe : P.PPe = Lv.PPeDef P
  hXW : P.XW = XWDef P
  hPinf : P.Pinf = Lv.PinfDef P
  he : ∀ q, P.e q = Lv.eDef P q

structure FieldTie (P : MeansPack Tau ι) (Lv : Leaves Tau) (E : Type) [Field E] [NumberField E] : Prop where
  hdeg : Module.finrank ℚ E = 2 * P.f
  hdisc : Lv.dE = (NumberField.discr E).natAbs

theorem FieldTie.dE_pos {P : MeansPack Tau ι} {Lv : Leaves Tau} {E : Type} [Field E] [NumberField E]
    (h : FieldTie P Lv E) : 1 ≤ Lv.dE := by
  rw [h.hdisc]
  exact Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)


theorem e_nonneg {P : MeansPack Tau ι} {Lv : Leaves Tau} (t : DefTie P Lv) (q : ℕ) : 0 ≤ P.e q := by
  rw [t.he]
  unfold Leaves.eDef
  exact (Finset.le_fold_max (0 : ℝ)).mpr (Or.inl le_rfl)



def packOf (P : MeansPack Tau ι) (Lv : Leaves Tau) (e : ℕ →₀ ℝ) : MeansPack Tau ι :=
  let P1 : MeansPack Tau ι :=
    { P with
      u1 := fun τ => firstGapVector P.N (Lv.bigp τ) Lv.A P.T P.D P.c0 (P.u τ)
      up := fun τ => upDef P.N (Lv.bigp τ) Lv.A P.T P.D P.c0 (P.u τ)
      rd := Lv.rdDef P
      vdd := Lv.vddDef P
      cpp := cppDef
      e := e }
  let P2 : MeansPack Tau ι := { P1 with PPe := Lv.PPeDef P1, XW := XWDef P1, Pinf := Lv.PinfDef P1 }
  { P2 with SB := Lv.SBDef P2 }


def basePack : MeansPack (Fin 1) (Fin 1) where
  N := 1
  f := 1
  T := 0
  D := 0
  jp := 0
  m := 1
  nc := 0
  u := 0
  u1 := 0
  up := 0
  c0 := 0
  b := Real.exp 4
  rd := 1
  x := Real.exp (Real.exp 1)
  Lp := 0
  h0 := 32
  fourthRootConstant := 0
  sl := 0
  e := 0
  SB := ∅
  cpp := 0
  vdd := 0
  Pinf := 0
  PPe := 0
  XW := 0

def baseLeaves : Leaves (Fin 1) where
  dE := 1
  level := 1
  q1 := 1
  d := 1
  g1 := 1
  g2 := 1
  rr := 1
  rr' := 1
  r0 := 1
  P0 := 0
  logmu := 0
  cubicPeriodConstant := 0
  c1 := 0
  Nc := 1
  bigp := fun _ => 1
  A := 0
  eloc := fun _ => ∅







end IxMeans.MeansTie
