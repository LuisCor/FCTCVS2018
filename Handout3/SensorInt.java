class SensorInt
{
    int value;
    int min;
    int max;
    
    Thread th;
    
    static final int SAMPLING = 3;
    
    SensorInt(int min, int max) 
    {
        this.min = min;
        this.max = max;
        this.value = min;
        this.th = new Thread(new Probe(this));
        this.th.start();
    }
    
    
    int get() 
    { 
        return this.value;
    }    
    
    void set(int value) 
    {
        this.value = value;
    }
    
    public static void main(String args[]) throws InterruptedException 
    {
        SensorInt s = new SensorInt(0,10);
        
        while(true)
        {
            // get and print a sample every 5 seconds
            
        }
    }
}