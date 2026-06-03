import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm
import Mathlib.Data.List.Sort
import Mathlib.Tactic


open List
open BigOperators
open Finset

/-
1. Определение контекста и предположений
1.1. Зафиксировать тип элементов α, для которых работает сортировка подсчётом.
1.2. Ввести верхнюю границу значений k : ℕ и предположить, что все элементы списка принадлежат множеству {0, 1, ..., k-1} (например, fin k или ℕ с условием < k).
1.3. Убедиться, что тип α имеет разрешимое равенство (нужно для подсчёта).

2. Определение подсчёта частот
2.1. Определить функцию count : list α → α → ℕ, считающую вхождения элемента в список.
2.2. Доказать: свойства count (например, count (x::xs) y = if x = y then count xs y + 1 else count xs y).

3. Построение массива частот
3.1. Определить функцию freq_array : list α → array (fin k) ℕ (или list ℕ длины k), вычисляющую для каждого возможного значения количество вхождений.
3.2. Доказать: для каждого v : fin k сумма частот по всем значениям от 0 до v равна количеству элементов списка, не превосходящих v.

4. Определение префиксных сумм (cumulative frequencies)
4.1. Определить функцию prefix_sums : list ℕ → list ℕ, преобразующую список частот в список накопленных сумм.
4.2. Доказать: связь между префиксными суммами и количеством элементов ≤ некоторого порога.

5. Определение функции построения отсортированного списка
5.1. Определить counting_sort_aux, которая по префиксным суммам и исходному списку строит отсортированный список (двигаясь справа налево, чтобы сортировка была устойчивой — если нужно).
5.2. Доказать: на каждом шаге инвариант о текущих позициях элементов.

6. Главная функция counting_sort
6.1. Объединить:
вычисление частот
вычисление префиксных сумм
построение результата.
6.2. Указать, что результат имеет длину, равную длине исходного списка.

7. Доказательство корректности
7.1. Сформулировать главную теорему:
Для любого списка l : list α и верхней границы k (где все элементы < k) результат counting_sort l k отсортирован по неубыванию и является перестановкой l.

7.2. Доказательство сортированности:
 7.2.1. Показать, что итоговый список состоит из элементов, последовательно выложенных в порядке возрастания их значений.
 7.2.2. Использовать свойства префиксных сумм для обоснования порядка.

7.3. Доказательство сохранения мультимножества:
 7.3.1. Показать, что каждый элемент из l попадает в результат ровно один раз.
 7.3.2. Использовать лемму о сумме частот, равной длине списка.

7.4. Доказательство устойчивости (опционально):
 7.4.1. Если проход идёт справа налево, показать, что относительный порядок равных элементов сохраняется.

8. Доказательство завершения и сложности (опционально)
8.1. Показать, что все рекурсии/итерации завершаются (по индукции на длину списка или по значению счётчика).
8.2. (Необязательно) Оценить количество операций: O(n + k).

9. Особые случаи и ограничения
9.1. Доказать: если входной список содержит элемент ≥ k, то сортировка подсчётом некорректна (или выдать ошибку).
9.2. Доказать: если k значительно больше длины списка, алгоритм всё ещё работает, но неэффективен по памяти.

10. Итоговое оформление
10.1. Упаковать всё в модуль counting_sort.
10.2. Сделать главную теорему удобной для использования (например, с автоматическим выводом контекста).
10.3. Проверить на нескольких примерах (можно вычислить внутри Lean).
-/
--Фиксируем тип α с разрешимым равенством
variable {α : Type} [DecidableEq α]
-- элементы типа α, есть функция val : α → ℕ с условием val a < k
variable (k : ℕ) (val : α → ℕ) (hval : ∀ a, val a < k)

/-
2. Определение подсчёта частот
-/
def my_count (xs : List α) (a : α) : ℕ := sorry
def freq_array (k : ℕ) (xs : List (Fin k)) : List ℕ := sorry
def prefix_sums (freqs : List ℕ) : List ℕ := sorry
def counting_sort (k : ℕ) (xs : List (Fin k)) : List (Fin k) := sorry
--2.2. Свойства count
lemma my_count_nil (a : α) : my_count [] a = 0 := by
  simp [my_count]

lemma my_count_cons_eq (x a : α) (xs : List α) (h : x = a) :
    my_count (x :: xs) a = my_count xs a + 1 := by
  simp [my_count]
  rw [if_pos h]
  exact Nat.one_add (my_count xs a)

lemma my_count_cons_ne (x a : α) (xs : List α) (h : x ≠ a) :
    my_count (x :: xs) a = my_count xs a := by
  simp [my_count]
  exact h

lemma my_count_cons (x a : α) (xs : List α) :
    my_count (x :: xs) a = (if x = a then my_count xs a + 1 else my_count xs a) := by
  simp [my_count]
  split
  next h => exact Nat.one_add (my_count xs a)
  next h => exact Nat.zero_add (my_count xs a)

lemma my_count_append (xs ys : List α) (a : α) :
    my_count (xs ++ ys) a = my_count xs a + my_count ys a := by
  induction xs with
  | nil => simp [my_count]
  | cons x xs ih =>
    simp [my_count, ih]
    split <;> simp [Nat.add_assoc]

lemma my_count_eq_countP (xs : List α) (a : α) :
    my_count xs a = countP (· = a) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [my_count, countP]
        simp
        rw [ih]
        by_cases h : x = a
        · simp [h]
        · simp [h]

lemma my_count_perm (xs ys : List α) (h : Perm xs ys) (a : α) :
    my_count xs a = my_count ys a := by
  rw [my_count_eq_countP, my_count_eq_countP]
  exact Perm.countP_eq (fun x ↦ decide (x = a)) h


--3.1. Функция freq_array возвращает список длины k,
-- где i-й элемент — количество вхождений в xs элемента a такого, что val a = i.

def freq_array (xs : List (Fin k)) : List ℕ :=
  List.ofFn (λ (i : Fin k) => my_count xs i)

lemma freq_array_length (k : ℕ) (xs : List (Fin k)) :
    (freq_array k xs).length = k := by
  simp [freq_array]

-- 3.2. Сумма частот равна длине списка
-- Вспомогательная лемма: сумма массива с увеличенным i-м элементом на 1
lemma sum_set_inc (arr : List ℕ) (i : ℕ) (h : i < arr.length) :
    (List.set arr i (List.get arr ⟨i, h⟩ + 1)).sum = arr.sum + 1 := by
  induction arr generalizing i with
  | nil =>
    simp at h
  | cons a as ih =>
    cases i with
    | zero =>
      simp [List.set, List.sum]
      sorry
      -- rw [Nat.add_assoc]
      -- rw [Nat.add_comm 1 as.sum]
      -- rw [← Nat.add_assoc]
      -- rfl
    | succ i' =>
      simp [List.set, List.sum]
      have h' : i' < as.length := by
        simp at h
        exact Nat.succ_lt_succ_iff.mp h
      refine (Nat.bit0_inj ?cons.succ.a).symm
      apply?
      rfl

lemma sum_freq_eq_length (k : ℕ) (xs : List (Fin k)) :
    (freq_array k xs).sum = xs.length := by
  induction xs with
  | nil =>
    unfold freq_array
    simp [List.replicate, List.sum]
    rfl
  | cons x xs ih =>
    unfold freq_array
    simp
    let arr := freq_array xs
    have h_len : x.val < arr.length := by
      simp [arr, freq_array]
      exact x.isLt
    rw [sum_set_inc arr x.val h_len]
    simp [ih]
/- 4. Префиксные суммы -/

def prefix_sums (freqs : List ℕ) : List ℕ :=
  List.scanl (· + ·) 0 freqs

-- 4.2. Свойства префиксных сумм

lemma prefix_sums_nth (freqs : List ℕ) (i : ℕ) :
    (prefix_sums freqs).get? i = some ((freqs.take i).sum) := by
  unfold prefix_sums
  induction freqs generalizing i
  case nil =>
    simp [List.scanl]
    cases i <;> sorry
  case cons x xs ih =>
    simp [List.scanl]
    rcases i with ⟨⟩ | i'
    · rfl
    · sorry
/-
5. Построение отсортированного списка
-/
def list_insertAt {α : Type} (lst : List α) (i : ℕ) (x : α) : List α :=
  let rec insert (n : ℕ) (l : List α) : List α :=
    match l with
    | [] => [x]
    | y :: ys =>
      if n = 0 then x :: y :: ys
      else y :: insert (n - 1) ys
  insert i lst

def counting_sort_aux (k : ℕ) (xs : List (Fin k)) (pref : List ℕ) : List (Fin k) :=
  let rec build (ys : List (Fin k)) (positions : List ℕ) (acc : List (Fin k)) : List (Fin k) :=
    match ys with
    | [] => acc
    | y :: rest =>
      match positions.get? (y.val) with
      | none => acc
      | some p =>
        let idx := p - 1
        let new_positions := positions.set (y.val) idx
        build rest new_positions (list_insertAt acc idx y)
  build xs.reverse pref []

lemma counting_sort_aux_length (k : ℕ) (xs : List (Fin k)) (pref : List ℕ)
    (h_pref : pref.length = k + 1) :
    (counting_sort_aux k xs pref).length = xs.length := by
  unfold counting_sort_aux
  let n := xs.length
  let rec build_len (ys : List (Fin k)) (positions : List ℕ) (result : Array (Option (Fin k)))
      (h_positions : positions.length = k)
      (h_result : result.size = n) :
      (build ys positions result).toList.filterMap id |>.length + ys.length = n := by
    induction ys generalizing positions result with
    | nil =>
      simp [build]
      rw [List.filterMap_id_eq]
      · simp [h_result]
      · intro x; simp
    | cons y ys ih =>
      simp [build]
      let idx := (positions.get (y.val)) - 1
      let new_positions := positions.set (y.val) idx
      have h_idx : idx < n := by
        have h1 : positions.get (y.val) ≤ positions.get? (y.val) := sorry
        have h2 : positions.get (y.val) ≤ pref.get (y.val) := sorry
        have h3 : pref.get (y.val) = (freq_array k xs).take (y.val).sum := by
          rw [← prefix_sums_nth]
          sorry
        sorry
      have h_new_positions : new_positions.length = k := by
        simp [new_positions, h_positions]
      have h_new_result : (result.set idx (some y)).size = n := by
        simp [Array.size_set, h_result]
      specialize ih new_positions (result.set idx (some y)) h_new_positions h_new_result
      simp [Array.toList_set] at ih
      rw [List.filterMap_id_eq] at ih
      · simp [ih]
        omega
      · intro x; simp
  have h_pref_len := h_pref
  have h_freq_len : (freq_array k xs).length = k := by apply freq_array_length
  have h_positions : pref.length = k + 1 := h_pref
  have h_result : (Array.mkArray n none).size = n := by simp
  specialize build_len xs.reverse pref (Array.mkArray n none) (by sorry) h_result
  simp [build_len]

lemma counting_sort_sorted (k : ℕ) (xs : List (Fin k)) :
    List.Sorted (· ≤ ·) (counting_sort k xs) := by
  unfold counting_sort
  let freqs := freq_array k xs
  let pref := prefix_sums freqs
  unfold counting_sort_aux

  -- Доказываем, что результирующий список отсортирован
  suffices ∀ i j, i < j →
    ((build xs.reverse pref (Array.mkArray xs.length none)).toList.filterMap id).get? i ≤
    ((build xs.reverse pref (Array.mkArray xs.length none)).toList.filterMap id).get? j by
    intro i j h_ij
    exact this i j h_ij

  let rec build_sorted (ys : List (Fin k)) (positions : List ℕ) (result : Array (Option (Fin k)))
      (h_positions : ∀ v, positions.get v = (freqs.take v).sum + (my_count (ys.reverse) v))
      (h_result : ∀ idx, result.get idx = none ↔ idx ∉ (positions.map (· - 1))) :
      ∀ i j, i < j →
        let res := (build ys positions result).toList.filterMap id
        res.get? i ≤ res.get? j := by
    induction ys generalizing positions result with
    | nil =>
      simp [build]
      intro i j h_ij
      have h_res : (result.toList.filterMap id).get? i ≤ (result.toList.filterMap id).get? j := by
        -- По инварианту h_result, элементы расположены в порядке возрастания
        sorry
      exact h_res
    | cons y ys ih =>
      simp [build]
      let idx := (positions.get (y.val)) - 1
      let new_positions := positions.set (y.val) idx
      let new_result := result.set idx (some y)
      have h_new_positions : ∀ v, new_positions.get v = (freqs.take v).sum + (my_count (ys.reverse) v) := by
        intro v
        simp [new_positions]
        by_cases v = y.val
        · subst h
          simp [positions.get]
          have h_pos := h_positions y.val
          have h_count : my_count (y :: ys).reverse y.val = my_count (ys.reverse) y.val + 1 := by
            sorry
          simp [h_pos, h_count]
        · simp [h_positions v]
      have h_new_result : ∀ idx', new_result.get idx' = none ↔ idx' ∉ (new_positions.map (· - 1)) := by
        intro idx'
        simp [new_result, Array.get_set]
        split
        · next h_eq =>
          simp [h_eq]
          constructor
          · intro h
            simp [new_positions]
            sorry
          · intro h
            simp [new_positions] at h
            sorry
        · next h_neq =>
          simp [h_neq]
          apply h_result
      specialize ih new_positions new_result h_new_positions h_new_result
      exact ih

  have h_pref_len : pref.length = k + 1 := by
    simp [pref, prefix_sums, freq_array_length]

  have h_positions : ∀ v, pref.get v = (freqs.take v).sum := by
    intro v
    have v_lt : v < pref.length := by simp [h_pref_len]; exact v.isLt
    have h_get := prefix_sums_nth freqs v
    simp [pref] at h_get
    exact h_get

  let n := xs.length
  let init_result := Array.mkArray n none
  let init_positions := pref

  have h_init_result : ∀ idx, init_result.get idx = none ↔ idx ∉ (init_positions.map (· - 1)) := by
    intro idx
    simp [init_result, Array.get_mkArray]
    constructor
    · intro h
      simp_all
    · intro h
      simp_all

  have h_init_positions : ∀ v, init_positions.get v = (freqs.take v).sum + (my_count (xs.reverse).reverse v) := by
    intro v
    simp [my_count]
    have h_rev : (xs.reverse).reverse = xs := by simp
    rw [h_rev]
    exact h_positions v

  let build_sorted_result := build_sorted xs.reverse init_positions init_result
    h_init_positions h_init_result

  exact build_sorted_result

lemma counting_sort_perm (k : ℕ) (xs : List (Fin k)) :
    Perm (counting_sort k xs) xs := by
  unfold counting_sort
  let freqs := freq_array k xs
  let pref := prefix_sums freqs
  unfold counting_sort_aux

  let rec build_perm (ys : List (Fin k)) (positions : List ℕ) (result : Array (Option (Fin k)))
      (h_positions : ∀ v, positions.get v = (freqs.take v).sum + (my_count (ys.reverse) v))
      (h_result : ∀ v, my_count (result.toList.filterMap id) v = my_count xs v - my_count ys v) :
      (build ys positions result).toList.filterMap id ++ ys ~ xs := by
    induction ys generalizing positions result with
    | nil =>
      simp [build]
      have h_res : (result.toList.filterMap id) ~ xs := by
        apply Perm.counts_eq
        intro v
        specialize h_result v
        simp at h_result
        exact h_result
      exact h_res
    | cons y ys ih =>
      simp [build]
      let idx := (positions.get (y.val)) - 1
      let new_positions := positions.set (y.val) idx
      let new_result := result.set idx (some y)

      have h_new_positions : ∀ v, new_positions.get v = (freqs.take v).sum + (my_count (ys.reverse) v) := by
        intro v
        simp [new_positions]
        by_cases v = y.val
        · subst h
          simp [positions.get]
          have h_pos := h_positions y.val
          have h_count : my_count (y :: ys).reverse y.val = my_count (ys.reverse) y.val + 1 := by
            simp [my_count, reverse_cons]
            sorry
          simp [h_pos, h_count]
        · simp [h_positions v]

      have h_new_result : ∀ v, my_count (new_result.toList.filterMap id) v = my_count xs v - my_count ys v := by
        intro v
        simp [new_result, Array.toList_set]
        by_cases v = y.val
        · subst h
          simp [my_count]
          have h_res := h_result y.val
          have h_count : my_count xs y.val - my_count (y :: ys) y.val =
                        my_count xs y.val - (my_count ys y.val + 1) := by
            simp [my_count]
            sorry
          rw [h_res, h_count]
          sorry
        · simp [h_result v]

      specialize ih new_positions new_result h_new_positions h_new_result
      simp at ih
      have h_perm : new_result.toList.filterMap id ++ ys ~ y :: xs := by
        sorry
      exact h_perm

  have h_pref_len : pref.length = k + 1 := by
    simp [pref, prefix_sums, freq_array_length]

  have h_positions : ∀ v, pref.get v = (freqs.take v).sum := by
    intro v
    have v_lt : v < pref.length := by simp [h_pref_len]; exact v.isLt
    have h_get := prefix_sums_nth freqs v
    simp [pref] at h_get
    exact h_get

  let n := xs.length
  let init_result := Array.mkArray n none
  let init_positions := pref

  have h_init_result : ∀ v, my_count (init_result.toList.filterMap id) v = my_count xs v - my_count xs.reverse v := by
    intro v
    simp [init_result]
    have h_rev : my_count xs.reverse v = my_count xs v := by
      apply my_count_perm
      exact Perm.reverse xs
    simp [h_rev]

  have h_init_positions : ∀ v, init_positions.get v = (freqs.take v).sum + (my_count (xs.reverse).reverse v) := by
    intro v
    simp [my_count]
    have h_rev : (xs.reverse).reverse = xs := by simp
    rw [h_rev]
    exact h_positions v

  let build_perm_result := build_perm xs.reverse init_positions init_result
    h_init_positions h_init_result

  exact build_perm_result

theorem counting_sort_correct (k : ℕ) (xs : List (Fin k)) :
    List.Sorted (· ≤ ·) (counting_sort k xs) ∧ Perm (counting_sort k xs) xs :=
  ⟨counting_sort_sorted k xs, counting_sort_perm k xs⟩
