struct Gfx {
  void opMoveSetShowText();
};

struct Operator {
  void (Gfx::*func)();
};

Operator opTab[] = {
  {&Gfx::opMoveSetShowText},
};

