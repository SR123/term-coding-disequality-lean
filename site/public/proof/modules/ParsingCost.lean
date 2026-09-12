import Parsing

/-! # Bit cost of parsing

Cost functions for the decoders of `Parsing.lean`, one per definition with the same
recursion shape, in the model of `EncodingCost.lean`:

* every input cell examined costs `1` (a `match` on the list);
* the natural counters (`c` in `decodeNatAux`/`readBits`, `n` in `decodeN`) are binary
  numbers; each increment, decrement or pattern match on one costs its bit length `natC`;
* `fromBits` is a fold of shift-and-add steps; each step costs the bit length of the
  partial value (`natC`), so the fold of `c` digits costs `O(c²)`;
* the canonicity check scans the digit string once.

No decoder measures the remaining input, so no cost depends on the unread tail.
`Consumes K f fc` says that `fc l ≤ K · (bits consumed)² + K` — all of the input on
failure — and that the remainder never grows; it is preserved by the combinators
(`consumes_bind`, `consumes_decodeN`, `consumes_decodeList`).  The full parser is
therefore quadratic in the input length on *every* bit string (`decodeInputC_le`), and
the parse-then-decide procedure is polynomial on every bit string (`decideBitsC_le_all`). -/

namespace DisequalityDispersion.Encoded

variable {α β : Type}

/-- Bits consumed by `f` on `l` (all of them on failure). -/
def consumed (f : List Bool → Option (α × List Bool)) (l : List Bool) : ℕ :=
  l.length - (match f l with | none => 0 | some (_, rest) => rest.length)

/-- Quadratic cost in the consumed prefix, and no growth of the remainder. -/
def Consumes (K : ℕ) (f : List Bool → Option (α × List Bool)) (fc : List Bool → ℕ) : Prop :=
  ∀ l, fc l ≤ K * consumed f l ^ 2 + K ∧ ∀ a rest, f l = some (a, rest) → rest.length ≤ l.length

/-- Strict progress on success. -/
def Progress (f : List Bool → Option (α × List Bool)) : Prop :=
  ∀ l a rest, f l = some (a, rest) → rest.length < l.length

theorem consumed_le (f : List Bool → Option (α × List Bool)) (l : List Bool) :
    consumed f l ≤ l.length := Nat.sub_le _ _

theorem consumed_none {f : List Bool → Option (α × List Bool)} {l : List Bool} (h : f l = none) :
    consumed f l = l.length := by simp [consumed, h]

theorem consumed_some {f : List Bool → Option (α × List Bool)} {l : List Bool} {a : α}
    {rest : List Bool} (h : f l = some (a, rest)) : consumed f l = l.length - rest.length := by
  simp [consumed, h]

/-- Any decoder satisfying `Consumes` costs at most `K · |l|² + K` on every input. -/
theorem Consumes.le {K : ℕ} {f : List Bool → Option (α × List Bool)} {fc : List Bool → ℕ}
    (hf : Consumes K f fc) (l : List Bool) : fc l ≤ K * l.length ^ 2 + K := by
  have h1 := (hf l).1
  have h2 := Nat.pow_le_pow_left (consumed_le f l) 2
  have := Nat.mul_le_mul_left K h2
  omega

theorem Consumes.mono {K K' : ℕ} (h : K ≤ K') {f : List Bool → Option (α × List Bool)}
    {fc : List Bool → ℕ} (hf : Consumes K f fc) : Consumes K' f fc := by
  intro l
  refine ⟨?_, (hf l).2⟩
  have := (hf l).1
  have := Nat.mul_le_mul_right (consumed f l ^ 2) h
  omega

theorem sq_add_le (a b : ℕ) : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
  have : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
  omega

/-! ### Combinator costs -/

/-- Cost of `bindP f g`. -/
def bindPC (f : List Bool → Option (α × List Bool)) (fc : List Bool → ℕ)
    (gc : α → List Bool → ℕ) (l : List Bool) : ℕ :=
  fc l + (match f l with | none => 0 | some (a, rest) => gc a rest)

theorem consumes_pure (b : β) : Consumes 0 (pureP b) (fun _ => 0) := by
  intro l
  refine ⟨by simp, ?_⟩
  intro a rest h
  simp only [pureP, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]

theorem consumes_bind {K₁ K₂ : ℕ} {f : List Bool → Option (α × List Bool)} {fc : List Bool → ℕ}
    {g : α → List Bool → Option (β × List Bool)} {gc : α → List Bool → ℕ}
    (hf : Consumes K₁ f fc) (hg : ∀ a, Consumes K₂ (g a) (gc a)) :
    Consumes (K₁ + K₂) (bindP f g) (bindPC f fc gc) := by
  intro l
  obtain ⟨hc, hn⟩ := hf l
  cases hfl : f l with
  | none =>
      have e : bindP f g l = none := by simp [bindP, hfl]
      simp only [bindPC, hfl, e, add_zero]
      rw [consumed_none e]
      rw [consumed_none hfl] at hc
      refine ⟨by nlinarith, fun a rest h => by simp at h⟩
  | some p =>
      obtain ⟨a, rest⟩ := p
      have hle := hn a rest hfl
      rw [consumed_some hfl] at hc
      have e : bindP f g l = g a rest := bindP_of_eq hfl
      obtain ⟨gc1, gn⟩ := hg a rest
      simp only [bindPC, hfl, e]
      cases hgl : g a rest with
      | none =>
          rw [consumed_none hgl] at gc1
          rw [consumed_none (e.trans hgl)]
          refine ⟨?_, fun b rest' h => by simp at h⟩
          have e2 : l.length = (l.length - rest.length) + rest.length := by omega
          have hsq := sq_add_le (l.length - rest.length) rest.length
          rw [← e2] at hsq
          nlinarith
      | some q =>
          obtain ⟨b, rest'⟩ := q
          have hle' := gn b rest' hgl
          rw [consumed_some hgl] at gc1
          rw [consumed_some (e.trans hgl)]
          refine ⟨?_, fun b' rest'' h => by
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2]; exact hle'.trans hle⟩
          have e2 : l.length - rest'.length = (l.length - rest.length) + (rest.length - rest'.length) := by
            omega
          have hsq := sq_add_le (l.length - rest.length) (rest.length - rest'.length)
          rw [← e2] at hsq
          nlinarith

/-- Cost of `decodeN f n`: each round matches on the binary counter (`natC`), runs `f`, conses. -/
def decodeNC (f : List Bool → Option (α × List Bool)) (fc : List Bool → ℕ) :
    ℕ → List Bool → ℕ
  | 0, _ => 1
  | n + 1, l => 1 + natC (n + 1) +
      bindPC f fc (fun _ rest => bindPC (decodeN f n) (decodeNC f fc n) (fun _ _ => 1) rest) l

/-- `decodeN` is quadratic in the consumed prefix plus one counter operation per value. -/
theorem decodeN_bound {K : ℕ} {f : List Bool → Option (α × List Bool)} {fc : List Bool → ℕ}
    (hf : Consumes K f fc) (hp : Progress f) :
    ∀ (n : ℕ) (l : List Bool),
      decodeNC f fc n l ≤ (2 * K + 3) * consumed (decodeN f n) l ^ 2 + (2 * K + 3) +
        (consumed (decodeN f n) l + 1) * natC n ∧
      ∀ as rest, decodeN f n l = some (as, rest) → rest.length ≤ l.length
  | 0, l => by
      simp only [decodeN, decodeNC]
      refine ⟨by nlinarith, ?_⟩
      intro a rest h
      simp only [pureP, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
  | n + 1, l => by
      simp only [decodeN, decodeNC]
      obtain ⟨hc, hn⟩ := hf l
      have hmono : natC n ≤ natC (n + 1) := natC_mono (Nat.le_succ n)
      cases hfl : f l with
      | none =>
          have e : bindP f (fun a => bindP (decodeN f n) (fun as => pureP (a :: as))) l = none := by
            simp [bindP, hfl]
          simp only [bindPC, hfl, e, add_zero]
          rw [consumed_none e]
          rw [consumed_none hfl] at hc
          refine ⟨by nlinarith, fun a rest h => by simp at h⟩
      | some p =>
          obtain ⟨a, rest⟩ := p
          have hlt := hp l a rest hfl
          rw [consumed_some hfl] at hc
          have e : bindP f (fun a => bindP (decodeN f n) (fun as => pureP (a :: as))) l =
              bindP (decodeN f n) (fun as => pureP (a :: as)) rest := bindP_of_eq hfl
          obtain ⟨gc1, gn⟩ := decodeN_bound hf hp n rest
          simp only [bindPC, hfl, e]
          cases hgl : decodeN f n rest with
          | none =>
              have e2 : bindP (decodeN f n) (fun as => pureP (a :: as)) rest = none := by
                simp [bindP, hgl]
              rw [e2, consumed_none (e.trans e2)]
              rw [consumed_none hgl] at gc1
              dsimp only
              refine ⟨?_, fun b rest' h => by simp at h⟩
              have e3 : l.length = (l.length - rest.length) + rest.length := by omega
              have hsq := sq_add_le (l.length - rest.length) rest.length
              rw [← e3] at hsq
              have h1 : 1 ≤ l.length - rest.length := by omega
              have hK : (rest.length + 1) * natC n + natC (n + 1) ≤ (l.length + 1) * natC (n + 1) := by
                have := Nat.mul_le_mul_left (rest.length + 1) hmono
                have : (rest.length + 2) * natC (n + 1) ≤ (l.length + 1) * natC (n + 1) :=
                  Nat.mul_le_mul_right _ (by omega)
                nlinarith
              have hA := Nat.mul_le_mul_left (2 * K + 3) hsq
              have hB : (K + 3) * 1 ≤ (K + 3) * (l.length - rest.length) ^ 2 :=
                Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ h1)
              nlinarith
          | some q =>
              obtain ⟨as, rest'⟩ := q
              have hle' := gn as rest' hgl
              have e2 : bindP (decodeN f n) (fun as => pureP (a :: as)) rest = some (a :: as, rest') := by
                rw [bindP_of_eq hgl]; rfl
              rw [e2, consumed_some (e.trans e2)]
              rw [consumed_some hgl] at gc1
              dsimp only
              refine ⟨?_, fun b rest'' h => by
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                rw [← h.2]; exact hle'.trans hlt.le⟩
              have e3 : l.length - rest'.length = (l.length - rest.length) + (rest.length - rest'.length) := by
                omega
              have hsq := sq_add_le (l.length - rest.length) (rest.length - rest'.length)
              rw [← e3] at hsq
              have h1 : 1 ≤ l.length - rest.length := by omega
              have hK : (rest.length - rest'.length + 1) * natC n + natC (n + 1) ≤
                  (l.length - rest'.length + 1) * natC (n + 1) := by
                have := Nat.mul_le_mul_left (rest.length - rest'.length + 1) hmono
                have : (rest.length - rest'.length + 2) * natC (n + 1) ≤
                    (l.length - rest'.length + 1) * natC (n + 1) :=
                  Nat.mul_le_mul_right _ (by omega)
                nlinarith
              have hA := Nat.mul_le_mul_left (2 * K + 3) hsq
              have hB : (K + 3) * 1 ≤ (K + 3) * (l.length - rest.length) ^ 2 :=
                Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ h1)
              nlinarith

/-! ### The concrete decoders -/

/-- Cost of `readBits c l`: one cell and one counter decrement per digit. -/
def readBitsC : ℕ → List Bool → ℕ
  | 0, _ => 1
  | c + 1, [] => 1 + natC (c + 1)
  | c + 1, _ :: l => 1 + natC (c + 1) + readBitsC c l

/-- Cost of `fromBits`: a shift-and-add on the partial value per digit. -/
def fromBitsC : List Bool → ℕ
  | [] => 1
  | _ :: bs => 1 + natC (fromBits bs) + fromBitsC bs

/-- Cost of `Canon`: one scan for the last digit. -/
def canonC (bs : List Bool) : ℕ := bs.length + 1

def decodeNatAuxC : ℕ → List Bool → ℕ
  | c, true :: l => 1 + natC c + decodeNatAuxC (c + 1) l
  | c, false :: l => 1 + readBitsC c l +
      (match readBits c l with
        | none => 0
        | some (bs, _) => canonC bs + fromBitsC bs)
  | _, [] => 1

def decodeNatC (l : List Bool) : ℕ := decodeNatAuxC 0 l

theorem natC_of_lt_pow {n k : ℕ} (h : n < 2 ^ k) : natC n ≤ 2 * k + 1 := by
  unfold natC
  have := Nat.size_le.mpr h
  omega

theorem fromBitsC_le : ∀ (bs : List Bool), fromBitsC bs ≤ bs.length * (2 * bs.length + 2) + 1
  | [] => by simp [fromBitsC]
  | b :: bs => by
      simp only [fromBitsC, List.length_cons]
      have h1 := fromBitsC_le bs
      have h2 := natC_of_lt_pow (fromBits_lt bs)
      nlinarith

/-- `readBits` on a successful read consumes exactly `c` cells. -/
theorem readBitsC_le : ∀ (c : ℕ) (l : List Bool),
    readBitsC c l ≤ (min c l.length + 1) * (2 + natC c)
  | 0, l => by simp [readBitsC]; omega
  | c + 1, [] => by simp [readBitsC]
  | c + 1, b :: l => by
      simp only [readBitsC, List.length_cons]
      have ih := readBitsC_le c l
      have hm : natC c ≤ natC (c + 1) := natC_mono (Nat.le_succ c)
      have : min (c + 1) (l.length + 1) = min c l.length + 1 := by omega
      rw [this]
      have hp : (min c l.length + 1) * (2 + natC c) ≤ (min c l.length + 1) * (2 + natC (c + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith

/-- The counter never exceeds the consumed prefix plus the ones already counted. -/
theorem decodeNatAux_bound : ∀ (c : ℕ) (l : List Bool),
    decodeNatAuxC c l + c * c + 2 * c ≤ 5 * (c + consumed (decodeNatAux c) l) ^ 2 + 5 ∧
    ∀ n rest, decodeNatAux c l = some (n, rest) → rest.length < l.length
  | c, [] => by
      refine ⟨?_, fun n rest h => by simp [decodeNatAux] at h⟩
      simp only [decodeNatAuxC, consumed, decodeNatAux, List.length_nil, Nat.sub_self, add_zero]
      nlinarith
  | c, true :: l => by
      obtain ⟨h1, h2⟩ := decodeNatAux_bound (c + 1) l
      have e : decodeNatAux c (true :: l) = decodeNatAux (c + 1) l := rfl
      refine ⟨?_, fun n rest h => by
        rw [e] at h; have := h2 n rest h; simp only [List.length_cons]; omega⟩
      simp only [decodeNatAuxC, consumed, e, List.length_cons] at h1 ⊢
      have hnat := natC_le_linear c
      generalize hd : decodeNatAux (c + 1) l = d at h1 h2 ⊢
      cases d with
      | none => simp at h1 ⊢; nlinarith
      | some p =>
          obtain ⟨n, rest⟩ := p
          have := h2 n rest rfl
          simp at h1 ⊢
          have e3 : l.length + 1 - rest.length = (l.length - rest.length) + 1 := by omega
          rw [e3]
          nlinarith
  | c, false :: l => by
      have e : decodeNatAux c (false :: l) =
          match readBits c l with
          | none => none
          | some (bs, rest) => if Canon bs then some (fromBits bs, rest) else none := rfl
      have hr := readBitsC_le c l
      have hnat := natC_le_linear c
      cases hrb : readBits c l with
      | none =>
          have e' : decodeNatAux c (false :: l) = none := by rw [e, hrb]
          refine ⟨?_, fun n rest h => by rw [e'] at h; simp at h⟩
          rw [consumed_none e']
          simp only [decodeNatAuxC, hrb, List.length_cons, add_zero]
          have hm : min c l.length ≤ l.length := min_le_right _ _
          have hmc : min c l.length ≤ c := min_le_left _ _
          nlinarith
      | some p =>
          obtain ⟨bs, rest⟩ := p
          obtain ⟨hlen, hl⟩ := readBits_some c l bs rest hrb
          have hf := fromBitsC_le bs
          rw [hlen] at hf
          have hmin : min c l.length = c := by rw [hl, List.length_append, hlen]; omega
          rw [hmin] at hr
          by_cases hc : Canon bs = true
          · have e' : decodeNatAux c (false :: l) = some (fromBits bs, rest) := by
              rw [e, hrb]; simp [hc]
            refine ⟨?_, fun n rest' h => by
              rw [e'] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.2, hl, List.length_cons, List.length_append]; omega⟩
            rw [consumed_some e']
            simp only [decodeNatAuxC, hrb, canonC, hlen, List.length_cons]
            have : l.length + 1 - rest.length = c + 1 := by
              rw [hl, List.length_append, hlen]; omega
            rw [this]
            nlinarith
          · have e' : decodeNatAux c (false :: l) = none := by
              rw [e, hrb]; simp [hc]
            refine ⟨?_, fun n rest' h => by rw [e'] at h; simp at h⟩
            rw [consumed_none e']
            simp only [decodeNatAuxC, hrb, canonC, hlen, List.length_cons]
            have : c ≤ l.length := by rw [hl, List.length_append, hlen]; omega
            nlinarith

theorem consumes_decodeNat : Consumes 5 decodeNat decodeNatC := by
  intro l
  obtain ⟨h1, h2⟩ := decodeNatAux_bound 0 l
  simp only [Nat.zero_add, mul_zero, add_zero] at h1
  exact ⟨h1, fun a rest h => (h2 a rest h).le⟩

theorem progress_decodeNat : Progress decodeNat := fun l a rest h =>
  (decodeNatAux_bound 0 l).2 a rest h

def decodeListC (f : List Bool → Option (α × List Bool)) (fc : List Bool → ℕ) : List Bool → ℕ :=
  bindPC decodeNat decodeNatC (fun n => decodeNC f fc n)

/-- The announced count of a list is at most the number of bits that announced it, so the
counter operations of `decodeN` are absorbed into the quadratic bound. -/
theorem consumes_decodeList {K : ℕ} {f : List Bool → Option (α × List Bool)} {fc : List Bool → ℕ}
    (hf : Consumes K f fc) (hp : Progress f) :
    Consumes (2 * K + 10) (decodeList f) (decodeListC f fc) := by
  intro l
  obtain ⟨hc, hn⟩ := consumes_decodeNat l
  unfold decodeList decodeListC
  cases hfl : decodeNat l with
  | none =>
      have e : bindP decodeNat (fun n => decodeN f n) l = none := by simp [bindP, hfl]
      simp only [bindPC, hfl, e, add_zero]
      rw [consumed_none e]
      rw [consumed_none hfl] at hc
      refine ⟨by nlinarith, fun a rest h => by simp at h⟩
  | some p =>
      obtain ⟨n, rest⟩ := p
      have hle := hn n rest hfl
      have hlt := progress_decodeNat l n rest hfl
      have hnc : natC n = l.length - rest.length := decodeNat_natC l n rest hfl
      rw [consumed_some hfl] at hc
      have e : bindP decodeNat (fun n => decodeN f n) l = decodeN f n rest := bindP_of_eq hfl
      obtain ⟨gc1, gn⟩ := decodeN_bound hf hp n rest
      simp only [bindPC, hfl, e]
      cases hgl : decodeN f n rest with
      | none =>
          rw [consumed_none hgl] at gc1
          rw [consumed_none (e.trans hgl)]
          refine ⟨?_, fun b rest' h => by simp at h⟩
          have e2 : l.length = (l.length - rest.length) + rest.length := by omega
          have hsq := sq_add_le (l.length - rest.length) rest.length
          rw [← e2] at hsq
          rw [hnc] at gc1
          have h1 : 1 ≤ l.length - rest.length := by omega
          nlinarith
      | some q =>
          obtain ⟨as, rest'⟩ := q
          have hle' := gn as rest' hgl
          rw [consumed_some hgl] at gc1
          rw [consumed_some (e.trans hgl)]
          refine ⟨?_, fun b rest'' h => by
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2]; exact hle'.trans hle⟩
          have e2 : l.length - rest'.length = (l.length - rest.length) + (rest.length - rest'.length) := by
            omega
          have hsq := sq_add_le (l.length - rest.length) (rest.length - rest'.length)
          rw [← e2] at hsq
          rw [hnc] at gc1
          have h1 : 1 ≤ l.length - rest.length := by omega
          nlinarith

theorem progress_bind {f : List Bool → Option (α × List Bool)}
    {g : α → List Bool → Option (β × List Bool)} (hf : Progress f)
    (hg : ∀ a l b rest, g a l = some (b, rest) → rest.length ≤ l.length) : Progress (bindP f g) := by
  intro l b rest h
  cases hfl : f l with
  | none => simp [bindP, hfl] at h
  | some p =>
      obtain ⟨a, rest'⟩ := p
      rw [bindP_of_eq hfl] at h
      exact lt_of_le_of_lt (hg a rest' b rest h) (hf l a rest' hfl)

theorem progress_decodeList {K : ℕ} {f : List Bool → Option (α × List Bool)} {fc : List Bool → ℕ}
    (hf : Consumes K f fc) (hp : Progress f) : Progress (decodeList f) :=
  progress_bind progress_decodeNat (fun n l as rest h => (decodeN_bound hf hp n l).2 as rest h)

def decodePairC : List Bool → ℕ :=
  bindPC decodeNat decodeNatC (fun _ => bindPC decodeNat decodeNatC (fun _ _ => 0))

theorem consumes_decodePair : Consumes 10 decodePair decodePairC :=
  consumes_bind consumes_decodeNat (fun _ => consumes_bind consumes_decodeNat (fun _ => consumes_pure _))

theorem progress_decodePair : Progress decodePair :=
  progress_bind progress_decodeNat (fun _ l b rest h =>
    (consumes_bind consumes_decodeNat (fun _ => consumes_pure _) l).2 b rest h)

/-- Cost of `tagP`: one cell for the tag, then the selected branch. -/
def tagPC (f0c f1c : List Bool → ℕ) : List Bool → ℕ
  | [] => 1
  | false :: l => 1 + f0c l
  | true :: l => 1 + f1c l

theorem consumes_tag {K : ℕ} {f0 f1 : List Bool → Option (α × List Bool)} {f0c f1c : List Bool → ℕ}
    (h0 : Consumes K f0 f0c) (h1 : Consumes K f1 f1c) :
    Consumes (K + 1) (tagP f0 f1) (tagPC f0c f1c) := by
  intro l
  cases l with
  | nil => exact ⟨by simp [tagPC, consumed, tagP], fun a rest h => by simp [tagP] at h⟩
  | cons b l =>
      have key : ∀ (f : List Bool → Option (α × List Bool)) (fc : List Bool → ℕ),
          Consumes K f fc → tagP f0 f1 (b :: l) = f l → tagPC f0c f1c (b :: l) = 1 + fc l →
          tagPC f0c f1c (b :: l) ≤ (K + 1) * consumed (tagP f0 f1) (b :: l) ^ 2 + (K + 1) ∧
          ∀ a rest, tagP f0 f1 (b :: l) = some (a, rest) → rest.length ≤ (b :: l).length := by
        intro f fc hf e ec
        obtain ⟨hc, hn⟩ := hf l
        rw [ec]
        refine ⟨?_, fun a rest h => by
          rw [e] at h; have := hn a rest h; simp only [List.length_cons]; omega⟩
        simp only [consumed, e, List.length_cons] at hc ⊢
        generalize hd : f l = d at hc hn ⊢
        cases d with
        | none =>
            simp at hc ⊢
            have : K * l.length ^ 2 ≤ (K + 1) * (l.length + 1) ^ 2 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
            omega
        | some p =>
            obtain ⟨a, rest⟩ := p
            have := hn a rest rfl
            simp at hc ⊢
            have e3 : l.length + 1 - rest.length = (l.length - rest.length) + 1 := by omega
            rw [e3]
            have : K * (l.length - rest.length) ^ 2 ≤ (K + 1) * (l.length - rest.length + 1) ^ 2 :=
              Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
            omega
      cases b with
      | false => exact key f0 f0c h0 rfl rfl
      | true => exact key f1 f1c h1 rfl rfl

def decodeNodeC : List Bool → ℕ :=
  tagPC (bindPC decodeNat decodeNatC (fun _ _ => 0))
    (bindPC decodeNat decodeNatC
      (fun _ => bindPC (decodeList decodeNat) (decodeListC decodeNat decodeNatC) (fun _ _ => 0)))

theorem consumes_decodeNode : Consumes 26 decodeNode decodeNodeC :=
  consumes_tag
    ((consumes_bind consumes_decodeNat (fun i => consumes_pure (β := Node) (Node.src i))).mono
      (by norm_num))
    (consumes_bind consumes_decodeNat (fun f =>
      consumes_bind (consumes_decodeList consumes_decodeNat progress_decodeNat)
        (fun args => consumes_pure (β := Node) (Node.app f args))))

theorem progress_decodeNode : Progress decodeNode := by
  intro l a rest h
  cases l with
  | nil => simp [decodeNode, tagP] at h
  | cons b l =>
      cases b with
      | false =>
          have e : decodeNode (false :: l) = bindP decodeNat (fun i => pureP (.src i)) l := rfl
          rw [e] at h
          have := (consumes_bind consumes_decodeNat (fun i => consumes_pure (β := Node) (Node.src i)) l).2 a rest h
          simp only [List.length_cons]; omega
      | true =>
          have e : decodeNode (true :: l) = bindP decodeNat
            (fun f => bindP (decodeList decodeNat) (fun args => pureP (.app f args))) l := rfl
          rw [e] at h
          have := (consumes_bind consumes_decodeNat (fun f =>
            consumes_bind (consumes_decodeList consumes_decodeNat progress_decodeNat)
              (fun args => consumes_pure (β := Node) (Node.app f args))) l).2 a rest h
          simp only [List.length_cons]; omega

def decodeInstanceC : List Bool → ℕ :=
  bindPC (decodeList decodeNat) (decodeListC decodeNat decodeNatC) (fun _ =>
    bindPC (decodeList decodePair) (decodeListC decodePair decodePairC) (fun _ =>
      bindPC (decodeList decodeNode) (decodeListC decodeNode decodeNodeC) (fun _ =>
        bindPC decodeNat decodeNatC (fun _ =>
          bindPC decodeNat decodeNatC (fun _ =>
            bindPC decodeNat decodeNatC (fun _ =>
              bindPC (decodeList decodePair) (decodeListC decodePair decodePairC) (fun _ _ => 0)))))))

theorem consumes_decodeInstance : Consumes 200 decodeInstance decodeInstanceC :=
  Consumes.mono (by norm_num) <| consumes_bind (consumes_decodeList consumes_decodeNat progress_decodeNat) (fun _ =>
    consumes_bind (consumes_decodeList consumes_decodePair progress_decodePair) (fun _ =>
      consumes_bind (consumes_decodeList consumes_decodeNode progress_decodeNode) (fun _ =>
        consumes_bind consumes_decodeNat (fun _ =>
          consumes_bind consumes_decodeNat (fun _ =>
            consumes_bind consumes_decodeNat (fun _ =>
              consumes_bind (consumes_decodeList consumes_decodePair progress_decodePair)
                (fun _ => consumes_pure _)))))))

def decodeGC : List Bool → ℕ :=
  bindPC decodeInstance decodeInstanceC (fun _ =>
    bindPC (decodeList decodeNat) (decodeListC decodeNat decodeNatC) (fun _ _ => 0))

theorem consumes_decodeG : Consumes 220 decodeG decodeGC :=
  Consumes.mono (by norm_num) <| consumes_bind consumes_decodeInstance (fun _ =>
    consumes_bind (consumes_decodeList consumes_decodeNat progress_decodeNat)
      (fun _ => consumes_pure _))

def decodePair'C : List Bool → ℕ :=
  bindPC decodeNat decodeNatC (fun _ => bindPC decodeG decodeGC (fun _ _ => 0))

theorem consumes_decodePair' : Consumes 225 decodePair' decodePair'C :=
  Consumes.mono (by norm_num) <| consumes_bind consumes_decodeNat (fun _ =>
    consumes_bind consumes_decodeG (fun _ => consumes_pure _))

/-- Cost of `decodeInput`: the parse, then one match to check that nothing is left. -/
def decodeInputC (l : List Bool) : ℕ := decodePair'C l + 1

/-- **Parsing is quadratic on every bit string**: `decodeInputC l ≤ 225 · |l|² + 226`. -/
theorem decodeInputC_le (l : List Bool) : decodeInputC l ≤ 225 * l.length ^ 2 + 226 := by
  unfold decodeInputC
  have := consumes_decodePair'.le l
  omega

/-- Cost of `decideBits`: parse, then decide. -/
def decideBitsC (l : List Bool) : ℕ :=
  decodeInputC l + (match decodeInput l with | none => 0 | some (k, g) => g.strictDecidePC k)

/-- End-to-end charged cost on the encoder-produced input of `(k, g)`. -/
theorem decideBitsC_le (k : ℕ) (g : GInstance) :
    decideBitsC (encodeInput k g) ≤
      225 * (natC k + sizeG g) ^ 2 + 226 + 91000 * sizeG g ^ 6 + 3 * natC k := by
  unfold decideBitsC
  rw [decodeInput_encodeInput]
  have h1 := decodeInputC_le (encodeInput k g)
  rw [encodeInput_length] at h1
  have h2 := g.strictDecidePC_le k
  simp only
  omega

/-- **Total charged time on every bit string** — malformed, truncated, noncanonical or with
trailing bits included — with constants independent of `k` and `g`:
`decideBitsC bs ≤ 92000 · (|bs| + 1)^6`. -/
theorem decideBitsC_le_all (bs : List Bool) : decideBitsC bs ≤ 92000 * (bs.length + 1) ^ 6 := by
  unfold decideBitsC
  have h1 := decodeInputC_le bs
  have hL2 : bs.length ^ 2 ≤ (bs.length + 1) ^ 6 :=
    (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hL1 : 1 ≤ (bs.length + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  cases hd : decodeInput bs with
  | none => simp only [add_zero]; nlinarith
  | some p =>
      obtain ⟨k, g⟩ := p
      have hsz := decodeInput_sizes bs k g hd
      have h2 := g.strictDecidePC_le k
      have hS6 : sizeG g ^ 6 ≤ (bs.length + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have hk : natC k ≤ (bs.length + 1) ^ 6 := by
        calc natC k ≤ bs.length + 1 := by omega
          _ = (bs.length + 1) ^ 1 := (pow_one _).symm
          _ ≤ (bs.length + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      simp only
      nlinarith

end DisequalityDispersion.Encoded
