Inductive day : type :=
  Monday : day
| Tuesday : day
| Wednesday : day
| Thursday : day
| Friday : day
| Saturday : day
| Sunday : day.

Define next_day :=
  fun(d:day).
    match d with
      Monday => Tuesday
    | Tuesday => Wednesday
    | Wednesday => Thursday
    | Thursday => Friday
    | Friday => Saturday
    | Saturday => Sunday
    | Sunday => Monday
    end.

Classify join (next_day Monday) Tuesday.
Classify join (next_day Saturday) Sunday.
Classify join (next_day Sunday) Monday.
