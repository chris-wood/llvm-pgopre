#
# OVER2 test
#
# Logic: // w1 w2 w3 w4 -- w1 w2 w3 w4 w1 w2
#
FORWARD success;
FORWARD failure;
: try_0 0 = IF success ELSE failure ENDIF ;
: try_1b 1 = IF try_0 ELSE failure ENDIF ;
: try_2 2 = IF try_1b ELSE failure ENDIF ;
: try_3 3 = IF try_2 ELSE failure ENDIF ;
: try_4 4 = IF try_3 ELSE failure ENDIF ;
: try_1a 1 = IF try_4 ELSE failure ENDIF ;
: MAIN 0 1 2 3 4 OVER2 2 = IF try_1a ELSE failure ENDIF ;
