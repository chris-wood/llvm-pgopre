// Test that these initializers are handled efficiently

int test(int x) {
  const int XX[1000] = { 0, 0 };
  const char S [1000] = "foo";

  const int array[] = {
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
     17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 17, 23, 123, 123, 49, 
   };
   return array[x];
} 
